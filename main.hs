import System.Environment

main :: IO ()
main = runApp

runApp :: IO ()
runApp = do
    args <- getArgs
    case (args) of
        [path] -> fileParser path
        _ -> putStrLn $ "Invalid amount of parameters: " ++ (show (length args))

fileParser :: String -> IO ()
fileParser path = do
    code <- readFile path
    putStrLn code
