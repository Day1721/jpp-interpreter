{-# LANGUAGE LambdaCase #-}

module Runner where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Trans.Except

import qualified Data.Map as Map
import qualified Text.Read as Read

import TypeChecker

data VarValue 
    = VInt Integer
    | VBool Bool
    | VStr String
    | VFunc Pattern [Statement] RunnerRead
    | VTuple [Variable]
    | VVoid
    | VLibFunc ([Variable] -> RunnerMonad Variable)

data Variable = Variable {
    varValue :: VarValue,
    varType :: Type
}

newtype RunnerRead = RunnerRead {
    declVariables :: Map.Map String Variable
}

updateDeclVariables :: (Map.Map String Variable -> Map.Map String Variable) -> RunnerRead -> RunnerRead
updateDeclVariables f (RunnerRead v) = RunnerRead (f v)

type RunnerMonad r = ExceptT String (ReaderT RunnerRead IO) r

data RunStatementRes
    = NoReturn
    | Returned
    | ReturnedVal Variable


printFunc :: [Variable] -> RunnerMonad Variable 
printFunc [Variable (VStr s) _] = liftIO (putStr s) >> return (Variable VVoid TVoid)
printFunc _ = throwE "Invalid argument for print expected str"

stoiFunc :: [Variable] -> RunnerMonad Variable
stoiFunc [Variable (VStr s) _] = case Read.readMaybe s :: Maybe Integer of
    Just i -> return (Variable (VInt i) TInt)
    Nothing -> throwE ("Can't convert " ++ s ++ " to int")
stoiFunc _ = throwE "Invalid argument for stoi: expected str"

itosFunc :: [Variable] -> RunnerMonad Variable
itosFunc [Variable (VInt i) _] = return (Variable (VStr (show i)) TStr)
itosFunc _ = throwE "Invalid argument for itos: expected int"

startRead :: RunnerRead 
startRead = let 
    libFuncs = [
            ("print", TFunc TStr TVoid, VLibFunc printFunc),
            ("stoi", TFunc TStr TInt, VLibFunc stoiFunc),
            ("itos", TFunc TInt TStr, VLibFunc itosFunc)
        ]
    varMap = foldl (\m (n,t,v) -> Map.insert n (Variable v t) m) Map.empty libFuncs
    in RunnerRead varMap

runProgram :: Program -> IO ()
runProgram p = let 
    runned = runReaderT (runExceptT (runProgramM p)) startRead 
    in runned >>= \case
        Right () -> return ()
        Left s -> putStrLn ("Runtime error:" ++ s) 


-- TODO migrate to runStatements
runProgramM :: Program -> RunnerMonad ()
runProgramM p = void $ runStatements p

runExpression :: TypedExpr -> RunnerMonad Variable
runExpression e = ask >>= \s -> case getExpr e of
    EFunc pat block -> return $ Variable (VFunc pat block s) $ getType e
    EFuncE pat expr -> return $ Variable (VFunc pat [SRet $ Just expr] s) $ getType e
    ETuple l -> mapM runExpression l >>= \r -> return $ Variable (VTuple r) $ getType e
    EOr b1 b2 -> runExpression b1 >>= \b1Res ->
        case varValue b1Res of
            VBool b1b -> if b1b then return $ Variable (VBool True) $ getType e else runExpression b2
            _ -> throwE "Invalid type: expected Bool"
    EAnd b1 b2 -> runExpression b1 >>= \b1Res ->
        case varValue b1Res of
            VBool b1b -> if b1b then runExpression b2 else return $ Variable (VBool False) $ getType e
            _ -> throwE "Invalid type: expected Bool"
    ECompare left right oper -> 
        runExpression left >>= \leftRes ->
        runExpression right >>= \rightRes -> 
        let operFun = case oper of
                Lt -> (<)
                Le -> (<=)
                Gt -> (>)
                Ge -> (>=)
        in case (varValue leftRes, varValue rightRes) of 
            (VInt leftInt, VInt rightInt) -> return $ Variable (VBool $ operFun leftInt rightInt) $ getType e
            _ -> throwE "Invalid type: expected Int"
    EEqual left right oper -> 
        runExpression left >>= \leftRes ->
        runExpression right >>= \rightRes -> 
        let 
            operFun :: Eq a => a -> a -> Bool
            operFun = case oper of 
                Equal -> (==)
                NotEqual -> (/=)
            checkEquality :: Variable -> Variable -> RunnerMonad Bool
            checkEquality leftVal rightVal = case (varValue leftVal, varValue rightVal) of
                (VInt i, VInt j) -> return $ operFun i j
                (VBool l, VBool r) -> return $ operFun l r
                (VStr l, VStr r) -> return $ operFun l r
                (VTuple ls, VTuple rs) -> zipWithM checkEquality ls rs >>= \resl ->
                    return $ and resl
                _ -> throwE "Comparison of function is not allowed"
        in checkEquality leftRes rightRes >>= \res ->
            return (Variable (VBool res) (getType e))
    EIntOp left right oper ->
        runExpression left >>= \leftRes ->
        runExpression right >>= \rightRes ->
        let 
            operFun :: Integer -> Integer -> RunnerMonad Integer
            operFun = case oper of
                OpAdd -> \x -> return . (x +)
                OpSub -> \x -> return . (x -)
                OpMul -> \x -> return . (x *)
                OpDiv -> \x y -> if y == 0 then throwE "Division by zero" else return $ div x y
                OpPow -> \x -> return . (x ^)
                OpMod -> \x y -> if y == 0 then throwE "Division by zero" else return $ mod x y
        in case (varValue leftRes, varValue rightRes) of
            (VInt l, VInt r) -> operFun l r >>= \res -> 
                return (Variable (VInt res) (getType e))
            _ -> throwE "Invalid type of integer operation"
    ENeg expr -> 
        runExpression expr >>= \ex -> case varValue ex of
            VBool v -> return $ Variable (VBool $ not v) $ getType e
            _ -> throwE "Invalid type in operation"
    EVar varName -> ask >>= \m -> case Map.lookup varName (declVariables m) of
        Just v -> return v
        Nothing -> throwE $ "use of uninitialized variable " ++ varName
    EInt i -> return $ Variable (VInt i) $ getType e
    EStr str -> return $ Variable (VStr str) $ getType e
    ETrue -> return $ Variable (VBool True) $ getType e
    EFalse -> return $ Variable (VBool False) $ getType e
    ECall fun params -> mapM runExpression params >>= \runableParams ->
        runExpression fun >>= \f -> let 
            addPatVariables :: Pattern -> [Variable] -> RunnerRead -> RunnerRead
            addPatVariables pat var rRead = let 
                in case pat of 
                    PVar _ -> addVariables pat (head var) rRead
                    PList l -> foldl (\r' (p,v) -> addVariables p v r') rRead $ zip l var
                    PIgnore -> rRead
            in case varValue f of
                VFunc pars stmt vars -> local (addPatVariables pars runableParams . const vars) (runStatements stmt) >>= \case
                    ReturnedVal v -> return v
                    _ -> return (Variable VVoid TVoid)
                VLibFunc libFunc -> libFunc runableParams
                _ -> throwE "given variable is not callable"

addVariables :: Pattern -> Variable -> RunnerRead -> RunnerRead
addVariables p v r = case p of 
    PVar s -> updateDeclVariables (Map.insert s v) r
    PList l -> case varValue v of 
        VTuple vl -> foldl (\r' (p',v') -> addVariables p' v' r') r $ zip l vl
        _ -> undefined -- unreachable here (type checkering should fail here)
    PIgnore -> r
            
runStatements :: [Statement] -> RunnerMonad RunStatementRes
runStatements [] = return NoReturn
runStatements (h:t) = let 
    runStatement :: Statement -> RunnerMonad (RunStatementRes, RunnerRead -> RunnerRead)
    runStatement = \case
        SLet pat expr -> runExpression expr >>= \calcExp ->
            return (NoReturn, addVariables pat calcExp)
            return (NoReturn, addVariables pat p)
        SIf ifExpr th el -> runExpression ifExpr >>= \ifVal -> 
            case varValue ifVal of
                VBool b -> if b then runStatement th else runStatement el
                _ -> throwE "invalid type"
        SWhile loopExpr handle -> runExpression loopExpr >>= \loopVal ->
            case varValue loopVal of
                VBool b -> if b 
                    then runStatement handle >>= \(res, update) ->
                        case res of
                            NoReturn -> local update (runStatement (SWhile loopExpr handle))
                            _ -> return (res, id)
                    else runStatement SSkip
                _ -> throwE "invalid type"
        SFor var begin end handler -> runExpression begin >>= \b -> 
            case varValue b of
                VInt i -> let
                    properFor :: Integer -> RunnerMonad (RunStatementRes, RunnerRead -> RunnerRead)
                    properFor beg = runExpression end >>= \e -> 
                        case varValue e of
                            VInt j -> if beg > j then runStatement SSkip 
                                else let varI = Variable (VInt beg) TInt
                                    in local (updateDeclVariables $ Map.insert var varI) (runStatement handler) >>= \(res, _) ->
                                        case res of 
                                            NoReturn -> properFor $ beg+1
                                            _ -> return (res,id)
                            _ -> throwE "invalid type"
                    in properFor i
                _ -> throwE "invalid type"
        SBlock l -> runStatements l >>= \r -> return (r,id)
        SRet mExpr -> case mExpr of 
            Just expr -> runExpression expr >>= \e -> 
                return (ReturnedVal e, id)
            Nothing -> return (Returned, id)
        SExpr expr -> runExpression expr >>= \_ -> 
            return (NoReturn, id)
        SSkip -> return (NoReturn, id)
    in runStatement h >>= \(res, action) -> 
        case res of 
            NoReturn -> local action (runStatements t)
            _ -> return res
    
{-
runStatements = foldM (\v s -> case v of 
        NoReturn -> runStatement s
        _ -> return v
    ) NoReturn
runStatement :: Statement -> RunnerMonad RunStatementRes
runStatement stmt = case stmt of
    SLet pat expr -> undefined ""
    _ -> undefined
-}
