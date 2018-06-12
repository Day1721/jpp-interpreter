{-#LANGUAGE LambdaCase#-}

--TODO : deepLift on show

module TypeChecker where

import qualified AbsGrammar as AG
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.List as List
import Data.Maybe

import Control.Monad
import Control.Monad.State
import Control.Monad.Trans.Except

data Type
    = TInt
    | TBool
    | TStr
    | TTuple [Type]
    | TVar String
    | TFunc Type Type
    | TVoid
    deriving (Eq,Read)

instance Show Type where 
    show t = case t of 
        TInt -> "int"
        TBool -> "bool"
        TStr -> "str"
        TTuple l -> "(" ++ List.intercalate "," (map show l) ++ ")"
        TFunc from to -> show from ++ " -> " ++ show to
        TVar v -> v
        TVoid -> "()"

showType :: Type -> WorkerMonad String
showType t = show <$> deepLiftType t

showExpr :: TypedExpr -> WorkerMonad String
showExpr (TypedExpr t e) = showType t >>= \st -> 
    return $ "TypedExpr { getType = " ++ st ++", getExpr = " ++ show e ++ "}"

type Program = [Statement];
data Statement
    = SLet Pattern TypedExpr
    | SIf TypedExpr Statement Statement
    | SWhile TypedExpr Statement
    | SFor String TypedExpr TypedExpr Statement
    | SBlock [Statement]
    | SRet (Maybe TypedExpr)
    | SExpr TypedExpr
    | SSkip
    deriving (Show,Eq)

data TypedExpr = TypedExpr { getType :: Type, getExpr :: Expr }
    deriving (Show,Eq)

data Expr
    = EFunc Pattern [Statement]
    | EFuncE Pattern TypedExpr
    | ETuple [TypedExpr]
    | EOr TypedExpr TypedExpr
    | EAnd TypedExpr TypedExpr
    | ECompare TypedExpr TypedExpr CompareOperation
    | EEqual  TypedExpr TypedExpr EqualityOperation
    | EIntOp TypedExpr TypedExpr IntegerOperation
    | ENeg TypedExpr
    | EVar String
    | EInt Integer
    | EStr String
    | ETrue
    | EFalse
    | ECall TypedExpr [TypedExpr]
    deriving (Eq, Show)

data Pattern = PVar String | PList [Pattern] | PIgnore
    deriving(Show,Eq)

data IntegerOperation
    = OpAdd
    | OpSub
    | OpMul
    | OpDiv
    | OpMod
    | OpPow
    deriving (Show,Eq)

-- int (for now)
data CompareOperation
    = Le
    | Lt
    | Ge
    | Gt 
    deriving (Show,Eq)

fromAbsRelOp :: AG.RelOp -> Either CompareOperation EqualityOperation
fromAbsRelOp op = case op of 
    AG.OLT -> Left Lt
    AG.OLE -> Left Le
    AG.OGT -> Left Gt
    AG.OGE -> Left Ge
    AG.OEq -> Right Equal
    AG.ONEq -> Right NotEqual

-- polymorphic (int, bool, string, tuple)
data EqualityOperation
    = Equal
    | NotEqual
    deriving (Show,Eq)


startState :: WorkerState
startState = let 
    libFuncs = [
            ("print", TFunc TStr TVoid),
            ("stoi", TFunc TStr TInt),
            ("itos", TFunc TInt TStr)
        ]
    varMap = foldl (\m (n,t) -> Map.insert n t m) Map.empty libFuncs
    in WorkerState 0 Set.empty varMap Map.empty Nothing

parseTypes :: AG.Program -> Either String Program
parseTypes p = evalState (runExceptT (parseTypesM p)) startState


getRetType :: Type -> WorkerMonad Type
getRetType t = case t of
    TFunc _ to -> return to
    _ -> throwE "Given type does not have return type"

registerType :: String -> WorkerMonad ()
registerType str = modify $ updateVarTypes (Set.insert str)

unregisterType :: String -> WorkerMonad ()
unregisterType str = modify $ updateVarTypes (Set.delete str)

fromParserType :: AG.Type -> WorkerMonad Type
fromParserType t = case t of
    AG.TInt -> return TInt
    AG.TBool -> return TBool
    AG.TStr -> return TStr
    AG.TTuple h l -> TTuple <$> mapM fromParserType (h:l)
    AG.TVar (AG.Ident s) -> registerType s >> return (TVar s)
    AG.TFunc from to -> 
        fromParserType from >>= \f -> 
        TFunc f <$> fromParserType to
    AG.TVoid -> return TVoid


data CheckerType = CheckerType { getCType :: Type, isMade :: Bool }
    deriving (Show)

data WorkerState = WorkerState { 
    getFreeTypeNum :: Int, -- number n, so that type a{n} isn't used yet
    getVarTypes :: Set.Set String, 
    getMap :: Map.Map String Type, -- variables
    getTempTypesMap :: Map.Map String Type,
    getCurrFunType :: Maybe Type
} deriving (Show)

setFreeTypeNum :: Int -> WorkerState -> WorkerState
setFreeTypeNum i (WorkerState _ l m t funT) = WorkerState i l m t funT

setVarTypes :: Set.Set String -> WorkerState -> WorkerState
setVarTypes l (WorkerState i _ m t funT) = WorkerState i l m t funT

setMap :: Map.Map String Type -> WorkerState -> WorkerState
setMap m (WorkerState i l _ t funT) = WorkerState i l m t funT

setTempTypesMap :: Map.Map String Type -> WorkerState -> WorkerState
setTempTypesMap t (WorkerState i l m _ funT) = WorkerState i l m t funT

setCurrFunType :: Maybe Type -> WorkerState -> WorkerState
setCurrFunType funT (WorkerState i l m t _) = WorkerState i l m t funT


updateFreeTypeNum :: (Int -> Int) -> WorkerState -> WorkerState
updateFreeTypeNum h (WorkerState i l m t funT) = WorkerState (h i) l m t funT

updateVarTypes :: (Set.Set String -> Set.Set String) -> WorkerState -> WorkerState
updateVarTypes h (WorkerState i l m t funT) = WorkerState i (h l) m t funT

updateTypesMap :: (Map.Map String Type -> Map.Map String Type) -> WorkerState -> WorkerState
updateTypesMap h (WorkerState i l m t funT) = WorkerState i l (h m) t funT

updateTempTypesMap :: (Map.Map String Type -> Map.Map String Type) -> WorkerState -> WorkerState
updateTempTypesMap h (WorkerState i l m t funT) = WorkerState i l m (h t) funT


type WorkMonadBuilder s a = ExceptT String (State s) a
type WorkerMonad a = WorkMonadBuilder WorkerState a


getNewType :: WorkerMonad Type
getNewType = 
    get >>= \s -> 
    modify (updateFreeTypeNum (1+)) >> let
        t = "'a" ++ show (getFreeTypeNum s)
    in modify (updateVarTypes (Set.insert t)) >>
    return (TVar t)

setPatternTypes :: AG.Pattern -> Type -> WorkerMonad Pattern
setPatternTypes p t = case p of
    AG.PVar (AG.Ident v) -> let 
        in modify (updateTypesMap (Map.insert v t)) >> return (PVar v)
    AG.PList pl -> case t of
        TTuple tl -> PList <$> zipWithM setPatternTypes pl tl
        _ -> throwE "Incompatible pattern type"
    AG.PIgnore -> return PIgnore

initPatternTypes :: AG.Pattern -> WorkerMonad (Type, Pattern)
initPatternTypes p = -- modify (setTempTypesMap Map.empty) >>
    initPatternTypesM p >>= \r -> 
    -- modify (setTempTypesMap Map.empty) >> 
    return r

initPatternTypesM :: AG.Pattern -> WorkerMonad (Type, Pattern)
initPatternTypesM p = case p of
    AG.PVar (AG.Ident v) -> 
        get >>= \s -> 
        case Map.lookup v $ getMap s of
            Just t -> return (t, PVar v)
            Nothing -> getNewType >>= \t -> 
                modify (updateTypesMap $ Map.insert v t) >> 
                return (t, PVar v)
    AG.PList l -> mapM initPatternTypesM l >>= \rs -> 
        return (TTuple (map fst rs), PList $ map snd rs)
    AG.PIgnore -> getNewType >>= \t -> 
        return (t, PIgnore)


checkAssignment :: Type -> Type -> WorkerMonad ()
checkAssignment = undefined

occursInType :: String -> Type -> Bool
occursInType typename t = case t of
    TVar s -> typename == s
    TFunc from to -> occursInType typename from && occursInType typename to
    TTuple l -> any (occursInType typename) l
    _ -> False


checkAssignmentM :: Type -> Type -> WorkerMonad (Type,Type)
checkAssignmentM varType targetType =  case (varType, targetType) of
    (TInt, TInt) -> return (TInt, TInt)
    (TBool, TBool) -> return (TBool, TBool)
    (TStr, TStr) -> return (TStr, TStr)
    (TTuple varL, TTuple targetL) -> zipWithM checkAssignmentM varL targetL >>= \r -> return (TTuple (map fst r), TTuple (map snd r))
    (TFunc varFrom varTo, TFunc targetFrom targetTo) -> checkAssignmentM varFrom targetFrom >> 
        checkAssignmentM varTo targetTo
    (TVar varV, TVar targetV) -> get >>= \s ->
        if varV == targetV then return (TVar varV, TVar targetV) 
        else if Set.member varV (getVarTypes s)
        then if Set.member targetV (getVarTypes s)
            then throwE ("Invalid type assignment. Exected " ++ varV ++", but got " ++ targetV ++ ".")
            else case Map.lookup targetV (getTempTypesMap s) of
                Just t -> checkAssignmentM varType t >> 
                    return (varType, targetType)
                Nothing -> modify (updateTempTypesMap (Map.insert targetV varType)) >> 
                    return (varType, targetType)
        else undefined -- TODO    Is accessable?                        ??????                                          ?????
    (TVar varV, _) -> undefined
    (_, TVar targetV) -> undefined
    _ -> undefined


registerPattern :: AG.Pattern -> WorkerMonad (Pattern,Type)
registerPattern = \case 
    AG.PVar (AG.Ident v) -> get >>= \s ->
        case Map.lookup v (getMap s) of 
            Just t -> return (PVar v, t)
            Nothing -> getNewType >>= \t ->
                modify (updateTypesMap (Map.insert v t)) >>
                return (PVar v,t)
    AG.PList l -> case l of 
        [] -> return (PList [], TVoid)
        [t] -> registerPattern t
        _ ->mapM registerPattern l >>= \resList -> let 
            f = map fst resList
            s = map snd resList
            in return (PList f, TTuple s)
    AG.PIgnore -> getNewType >>= \t -> return (PIgnore,t)
    
throwInvalidType :: Monad m => Type -> Type -> ExceptT String m a
throwInvalidType expected got = throwE $ "Invalid type: expected " ++ show expected ++ " but got " ++ show got

unify :: Type -> Type -> WorkerMonad Type
unify lType rType = case (lType, rType) of
        (TInt, TInt) -> return TInt
        (TStr, TStr) -> return TStr
        (TBool, TBool) -> return TBool
        (TVoid, TVoid) -> return TVoid
        (TTuple ll, TTuple rl) -> zipWithM unify ll rl >>= \res ->
            return $ TTuple res
        (TFunc lfrom lto, TFunc rfrom rto) -> unify lfrom rfrom >>= \from ->
            unify lto rto >>= \to ->
            return $ TFunc from to
        (TVar a, _) -> get >>= \s ->
            case Map.lookup a $ getTempTypesMap s of
                Just t -> unify t rType
                Nothing -> modify (updateTempTypesMap $ Map.insert a rType) >>
                    return rType
        (_, TVar a) -> get >>= \s ->
            case Map.lookup a $ getTempTypesMap s of
                Just t -> unify lType t
                Nothing -> modify (updateTempTypesMap $ Map.insert a lType) >>
                    return lType
        _ -> throwE $ "Types " ++ show lType ++ " and " ++ show rType ++ " aren't unifieble"

clearTempTypes :: WorkerMonad ()
clearTempTypes = get >>= \s -> let
    varTypes = getVarTypes s 
    in modify $ updateTempTypesMap $ Map.filterWithKey $ \k _ -> 
        Set.member k varTypes

replaceVarType :: String -> Type -> WorkerMonad ()
replaceVarType var t = modify $ updateTypesMap (Map.insert var t) 
    . updateVarTypes (Set.delete var)

liftType :: Type -> WorkerMonad Type
liftType t = case t of
    TVar a -> get >>= \s -> 
        case Map.lookup a (getTempTypesMap s) of 
            Just t' -> liftType t'
            Nothing -> return $ TVar a
    _ -> return t

liftExpr :: TypedExpr -> WorkerMonad TypedExpr
liftExpr (TypedExpr t e) = liftType t >>= \tv -> return $ TypedExpr tv e

deepLiftType :: Type -> WorkerMonad Type
deepLiftType t = liftType t >>= \lt -> 
    case lt of
        TFunc from to -> deepLiftType from >>= \lfrom ->
            deepLiftType to >>= \lto ->
            return $ TFunc lfrom lto
        TTuple list -> mapM deepLiftType list >>= \llist ->
            return $ TTuple llist
        _ -> return lt
    

parseExpression :: AG.Expr -> WorkerMonad TypedExpr
parseExpression = let 
    parseIntOp :: AG.Expr -> AG.Expr -> IntegerOperation -> WorkerMonad TypedExpr
    parseIntOp left right op = parseExpression left >>= 
        liftExpr >>= \l -> 
        parseExpression right >>= 
        liftExpr >>= \r ->
        case (getType l, getType r) of
            (TInt, TInt) -> 
                return $ TypedExpr TInt $ EIntOp l r op
            (TInt, TVar a) -> 
                replaceVarType a TInt >>
                return (TypedExpr TInt $ EIntOp l (TypedExpr TInt $ getExpr r) op)
            (TInt, _) -> 
                throwInvalidType TInt $ getType r
            (TVar a, TInt) -> 
                replaceVarType a TInt >>
                return (TypedExpr TInt $ EIntOp (TypedExpr TInt $ getExpr l) r op)
            (TVar a, TVar b) -> 
                replaceVarType a TInt >>
                replaceVarType b TInt >>
                return (TypedExpr TInt $ EIntOp (TypedExpr TInt $ getExpr l) r op)
            _ -> throwInvalidType TInt $ getType l
    mergeFuncStates :: WorkerState -> WorkerState -> WorkerState
    mergeFuncStates before = setVarTypes (getVarTypes before) 
        . setMap (getMap before) 
        . setCurrFunType (getCurrFunType before)
    in \case 
        AG.EFunc pat stmt -> get >>= \s ->
            registerPattern pat >>= \(patVal, patType) -> 
            getNewType >>= \t -> 
            modify (setCurrFunType $ Just $ TFunc patType t) >>
            parseStatement (AG.SBlock stmt) >>= \resStmt ->
            get >>= \s' -> 
            modify (mergeFuncStates s) >> case resStmt of 
                SBlock stmts -> return $ TypedExpr (fromJust $ getCurrFunType s') (EFunc patVal stmts)
                _ -> return $ TypedExpr (fromJust $ getCurrFunType s') $ EFunc patVal [resStmt]
        AG.EFuncE pat expr -> get >>= \s ->
            registerPattern pat >>= \(patVal, patType) -> 
            parseExpression expr >>= \(TypedExpr t e) ->
            modify (mergeFuncStates s) >> 
            return (TypedExpr (TFunc patType t) $ EFuncE patVal $ TypedExpr t e)
        AG.ETuple (AG.TMany h t) -> mapM parseExpression (h:t) >>= \exprs -> let
            tupleType = TTuple $ map getType exprs 
            in return $ TypedExpr tupleType $ ETuple exprs
        AG.EOr left right -> parseExpression left >>= 
            liftExpr >>= \lexpr ->
            parseExpression right >>= 
            liftExpr >>= \rexpr -> let
                getRes le re = TypedExpr TBool $ EOr le re
                in case (getType lexpr, getType rexpr) of 
                    (TBool, TBool) -> 
                        return $ getRes lexpr rexpr
                    (TBool, TVar a) -> 
                        replaceVarType a TBool >>
                        return (getRes lexpr $ TypedExpr TBool $ getExpr rexpr)
                    (TBool, _) -> 
                        throwInvalidType TBool $ getType rexpr
                    (TVar a, TBool) -> 
                        replaceVarType a TBool >>
                        return (getRes (TypedExpr TBool $ getExpr lexpr) rexpr)
                    (TVar a, TVar b) -> 
                        replaceVarType a TBool >>
                        replaceVarType b TBool >>
                        return (getRes (TypedExpr TBool $ getExpr lexpr) $ TypedExpr TBool $ getExpr rexpr)
                    _ -> throwInvalidType TBool $ getType lexpr
        AG.EAnd left right -> parseExpression left >>= 
            liftExpr >>= \lexpr ->
            parseExpression right >>= 
            liftExpr >>= \rexpr -> let
                getRes le re = TypedExpr TBool $ EAnd le re
                in case (getType lexpr, getType rexpr) of 
                    (TBool, TBool) -> 
                        return $ getRes lexpr rexpr
                    (TBool, TVar a) -> 
                        replaceVarType a TBool >>
                        return (getRes lexpr $ TypedExpr TBool $ getExpr rexpr)
                    (TBool, _) -> 
                        throwInvalidType TBool $ getType rexpr
                    (TVar a, TBool) -> 
                        replaceVarType a TBool >>
                        return (getRes (TypedExpr TBool $ getExpr lexpr) rexpr)
                    (TVar a, TVar b) -> 
                        replaceVarType a TBool >>
                        replaceVarType b TBool >>
                        return (getRes (TypedExpr TBool $ getExpr lexpr) $ TypedExpr TBool $ getExpr rexpr)
                    _ -> throwInvalidType TBool $ getType lexpr
        AG.ERel left op right -> parseExpression left >>= 
            liftExpr >>= \lexpr ->
            parseExpression right >>= 
            liftExpr >>= \rexpr ->
            case fromAbsRelOp op of 
                Left comp -> let 
                    getRes le re = TypedExpr TBool $ ECompare le re comp
                    in case (getType lexpr, getType rexpr) of 
                        (TInt, TInt) -> 
                            return $ getRes lexpr rexpr
                        (TInt, TVar a) -> 
                            replaceVarType a TInt >>
                            return (getRes lexpr $ TypedExpr TInt $ getExpr rexpr)
                        (TInt, _) -> 
                            throwInvalidType TInt $ getType rexpr
                        (TVar a, TInt) -> 
                            replaceVarType a TInt >>
                            return (getRes (TypedExpr TInt $ getExpr lexpr) rexpr)
                        (TVar a, TVar b) ->
                            replaceVarType a TInt >>
                            replaceVarType b TInt >>
                            return (getRes (TypedExpr TInt $ getExpr lexpr) $ TypedExpr TInt $ getExpr rexpr)
                        _ -> throwInvalidType TInt $ getType lexpr
                Right eq -> let 
                    checker :: Type -> Type -> WorkerMonad ()
                    checker tleft tright = case (tleft, tright) of 
                        (TInt, TInt) -> return ()
                        (TBool, TBool) -> return ()
                        (TStr, TStr) -> return ()
                        (TTuple llist, TTuple rlist) -> zipWithM_ checker llist rlist
                        (TVar _, TVar _) -> throwE "Var types aren't comparable"
                        (TFunc _ _, _) -> throwE "(* -> *) types aren't comparable"
                        (_, TFunc _ _) -> throwE "(* -> *) types aren't comparable"
                        (TVar a, _) -> void $ replaceVarType a tright
                        (_, TVar a) -> void $ replaceVarType a tleft 
                        _ -> throwE $ "Types " ++ show tleft ++ " and " ++ show tright ++ " isn't comparable"

                    res = TypedExpr TBool $ EEqual lexpr rexpr eq 
                    in checker (getType lexpr) (getType rexpr) >> return res
        AG.EAdd left op right -> case op of 
            AG.OPlus -> parseIntOp left right OpAdd
            AG.OMinus -> parseIntOp left right OpSub
        AG.EMul left op right -> case op of 
            AG.OMult -> parseIntOp left right OpMul
            AG.ODiv -> parseIntOp left right OpDiv
            AG.OMod -> parseIntOp left right OpMod
        AG.EPow left op right -> case op of 
            AG.OPow -> parseIntOp left right OpPow
        AG.ENeg inner -> parseExpression inner >>= \res -> 
            case getType res of
                TBool -> return $ TypedExpr TBool $ ENeg res
                TVar a -> replaceVarType a TBool >> 
                    return (TypedExpr TBool $ ENeg $ TypedExpr TBool $ getExpr res)
                _ -> throwInvalidType TBool $ getType res
        AG.EVar (AG.Ident name) -> get >>= \s ->
            case Map.lookup name $ getMap s of
                Just t -> return (TypedExpr t (EVar name))
                Nothing -> throwE $ "Usage of undefined variable " ++ name
        AG.EInt v -> return $ TypedExpr TInt $ EInt v
        AG.EStr v -> return $ TypedExpr TStr $ EStr v
        AG.ETrue -> return $ TypedExpr TBool ETrue
        AG.EFalse -> return $ TypedExpr TBool EFalse
        AG.ECall funE params -> parseExpression funE >>= 
            liftExpr >>= \funExpr -> 
            mapM parseExpression params >>= \parsed -> let 
                paramsType = case map getType parsed of 
                    [] -> TVoid
                    [t] -> t
                    l -> TTuple l
                in case getType funExpr of
                    TFunc paramT retT -> unify paramT paramsType >> 
                            liftType retT >>= \retT' -> 
                            clearTempTypes >>
                            return (TypedExpr retT' $ ECall funExpr parsed)
                    TVar a -> getNewType >>= \retT -> let 
                        funcType = TFunc paramsType retT 
                        in replaceVarType a (TFunc paramsType retT) >>
                            return (TypedExpr retT $ ECall (TypedExpr funcType $ getExpr funExpr) parsed)
                    _ -> throwE $ "Expected (* -> *) type, but got " ++ show (getType funExpr)


parseTypesM :: AG.Program -> WorkerMonad Program
parseTypesM (AG.Prog stmts) =  mapM parseStatement stmts

parseStatement :: AG.Stmt -> WorkerMonad Statement
parseStatement stmt = case stmt of
    AG.SLet p e -> parseLet p e Nothing
    AG.SLetT p t e -> parseLet p e (Just t)
    AG.SIf i t -> parseIf i t Nothing
    AG.SIfEls i t e -> parseIf i t (Just e)
    AG.SWhile e s -> parseWhile e s
    AG.SFor (AG.Ident v) b e s -> parseFor v b e s
    AG.SBlock (AG.BBlock b) -> parseBlock b
    AG.SRet r -> parseRet (Just r)
    AG.SRetV -> parseRet Nothing
    AG.SExpr e -> SExpr <$> parseExpression e
    AG.SSkip -> return SSkip

parsePattern :: AG.Pattern -> WorkerMonad (Type, Pattern)
parsePattern = initPatternTypes
   

parseLet :: AG.Pattern -> AG.Expr -> Maybe AG.Type -> WorkerMonad Statement
parseLet pat expr _ = let 
    bindPatternExpr :: Pattern -> Type -> WorkerMonad ()
    bindPatternExpr patt exprType = liftType exprType >>= \t -> 
        case (patt,t) of
            (PVar v, _) -> modify (updateTypesMap $ Map.insert v exprType)
            (PIgnore, _) -> return ()
            (PList list, TTuple tuple) -> zipWithM_ bindPatternExpr list tuple
            (PList list, TVar a) -> mapM_ (\p -> getNewType >>= \t -> bindPatternExpr p t) list
            _ -> throwE ""
    in parsePattern pat >>= \(_ , tcPat) ->
        parseExpression expr >>= \tExpr ->
        bindPatternExpr tcPat (getType tExpr) >>
        return (SLet tcPat tExpr)

parseIf :: AG.Expr -> AG.Stmt -> Maybe AG.Stmt -> WorkerMonad Statement
parseIf eIf sThen msElse = parseExpression eIf >>= \teIf ->
    parseStatement sThen >>= \tcThen ->
    case msElse of
        Just sElse -> parseStatement sElse >>= \tcElse -> 
            return $ SIf teIf tcThen tcElse
        Nothing -> return $ SIf teIf tcThen SSkip

parseWhile :: AG.Expr -> AG.Stmt -> WorkerMonad Statement
parseWhile ePred sHandle = parseExpression ePred >>= \tePred ->
    parseStatement sHandle >>= \tcHandle ->
    return $ SWhile tePred tcHandle

parseFor :: String -> AG.Expr -> AG.Expr -> AG.Stmt -> WorkerMonad Statement
parseFor var from to handle = let 
    iterType = TInt
    in modify (updateTypesMap (Map.insert var iterType)) >>
        parseExpression from >>= \tcFrom ->
        parseExpression to >>= \tcTo ->
        parseStatement handle >>= \tcHandle ->
        return (SFor var tcFrom tcTo tcHandle)

parseBlock :: [AG.Stmt] -> WorkerMonad Statement
parseBlock stmts = get >>= \oldState ->
    mapM parseStatement stmts >>= \tcStmts ->
    get >>= \newState ->
    foldM_ (\_ k -> if Map.member k $ getMap oldState then return () else modify $ updateTypesMap $ Map.delete k) () (Map.keys $ getMap newState) >>
    foldM_ (\_ t -> if Set.member t $ getVarTypes oldState then return () else modify $ updateVarTypes $ Set.delete t) () (Set.toList $ getVarTypes newState) >>
    return (SBlock tcStmts)

parseRet :: Maybe AG.Expr -> WorkerMonad Statement
parseRet mExpr = get >>= \s ->
    case getCurrFunType s of
        Just t -> case mExpr of
            Just expr -> getRetType t >>= 
                liftType >>= \retT -> 
                parseExpression expr >>= 
                liftExpr >>= \typedExpr -> 
                unify (getType typedExpr) retT >>
                return (SRet $ Just typedExpr)
            Nothing -> getRetType t >>= 
                liftType >>= \retT -> 
                unify TVoid retT >>
                return (SRet Nothing) 
        Nothing -> throwE "Invalid return statement outside a function"
