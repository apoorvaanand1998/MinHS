-- Haskelly Test Script
-- BSD3
-- Copyright (C) Gabriele Keller 2020
-- Copyright (C) Liam O'Connor-Davis 2010

import Control.Exception

import System.Directory
import Control.Applicative((<$>))
import System.FilePath
import System.Environment
import Data.List
import Data.Maybe
import Control.Monad
import Diff
import System.Process
import System.Exit
import Data.Char

data Options = Options { optTests :: FilePath
                       , optColor :: Bool }

color opts v c | optColor opts = v ++ c ++ "\ESC[0m"
               | otherwise     = c

brightWhite = "\ESC[1;97m"
darkWhite   = "\ESC[37m"
darkRed     = "\ESC[31m"
brightRed   = "\ESC[1;91m"
brightGreen = "\ESC[1;92m"
darkYellow  = "\ESC[33m"

traverseP :: String -> IO [String]
traverseP path = do
   contents <- sort <$> getDirectoryContents path
   let sanitizedContents = map (path </>) $ contents \\ ["..","."]
   directories <- filterM doesDirectoryExist sanitizedContents
   files <- filterM doesFileExist sanitizedContents
   if null directories
     then return files
     else do
       traversal <- concat <$> mapM traverseP directories
       return $ traversal ++ files

foreach = flip mapM

showSummary options marks = color options brightWhite $
    if length marks > 0
      then "Passed " ++ show (length $ filter (/= 0) marks)
                     ++ " out of " ++ show (length marks)
                     ++ " tests: " ++ show (((length $ filter (/= 0) marks) * 100) `div` length marks)
                     ++ "% Correct. Total of " ++ show (sum marks) ++ " marks."
      else "No tests run."

getSkips skips = concat <$> (foreach skips $ \skip -> map (<.> ".mhs") .
                                                      map (takeDirectory skip </>) .
                                                      lines <$> readFile skip)

runTests options exename exeargs = do
    files <- traverseP $ optTests options
    let tests' = filter ((".mhs" ==) . takeExtension) files
    let skips  = filter (("Skip" ==) . takeBaseName) files
    tests <- (tests' \\) <$> getSkips skips
    marks <- foreach tests $ (\test -> do
      (expect_fail, flags) <- getFlags (test `replaceFileName` "Flag")
      mark <- getMarks (test `replaceFileName` "Marks")
      putStr $ color options brightWhite ("Running test: ")
                 ++ color options darkWhite (makeRelative (optTests options) test)
                 ++ color options brightWhite (" (worth " ++ show mark ++ ") :-  ")
      (exit, out, err) <- readCreateProcessWithExitCode (proc exename (exeargs ++ flags ++ ["--no-colour", test])) ""
      let check = do r1 <- doCheck ".out" "Stdout" test out
                     r2 <- doCheck ".err" "Stderr" test err
                     return $ r1 * r2 * mark
      case exit of
        ExitFailure i -> if expect_fail then check
                         else do putStrLn $ color options darkRed ("Executable returned non-zero exit code(" ++ show i ++ ").")
                                 dumpOutput err out
        ExitSuccess -> if not expect_fail
                          then check
                          else do putStrLn $ color options darkRed ("Expected program failure, but it unexpectedly succeeded.")
                                  dumpOutput err out)
    putStrLn $ showSummary options marks
  where
    dumpOutput err out = do
      putStrLn $ color options darkRed ("Stderr was:")
      putStrLn err
      putStrLn $ color options darkRed ("Stdout was:")
      putStrLn out
      return 0
    doCheck ext name test out = do
      v <- doesFileExist (test `replaceExtension` ext)
      if v
        then do
          diff <- getDiff (filter (not . all isSpace) $ lines out) <$> filter (not . all isSpace) . lines
                                                                   <$> readFile (test `replaceExtension` ".out")
          if all (== B) $ map fst diff
            then putStrLn (color options brightGreen $ name ++ " Check Passed!") >> return 1
            else do
              putStrLn $ (color options brightRed $ name ++ " Check Failed") ++ ":\n" ++ showDiff options diff
              return 0
        else if (not $ all isSpace out)
          then do
            putStrLn $ color options darkYellow $ "No " ++ ext ++ " file found. Printing output..."
            putStr out
            return 1
          else return 1

getFlags filename = do
  v <- doesFileExist filename
  if v then do
         str <- lines <$> readFile filename
         return ("expect-fail" `elem` str, delete "expect-fail" str)
       else return (False, [])

getMarks filename = let readInteger s = case reads s of
                                            [(a,b)] -> a
                                            _       -> 1
                     in do v <- doesFileExist filename
                           if v then  readInteger <$> readFile filename
                                else return 1

parseArgs :: [String] -> Either String (Options, [String])
parseArgs = go Options { optTests = "tests", optColor = True }
  where go opts ("-t" : path : args) = go opts { optTests = path } args
        go opts ["-t"] = Left "The `-t' option expects an argument"
        go opts ("--no-color" : args) = go opts { optColor = False } args
        go opts args = Right (opts, args)

main = do
  cd <- getCurrentDirectory
  v <- getArgs
  when (v == [ "--help" ] || v == [ "-h" ]) $ do
     putStrLn $ "Liam's Haskelly Test Runner v0.1. \n" ++
                "This program is usually accompanied by a runner shell script.\n" ++
                "  Usage: ./run_tests.sh [--no-color] [-t <test_folder_location>] [program_to_test...]\n\n" ++
                "If no shell script is available, it can be run easily via runhaskell:\n" ++
                "  Usage: runhaskell -i./tests/driver ./tests/driver/Check.hs [--no-color] [-t <test_folder_location>] [program_to_test...]"
     exitSuccess
  (options, execmd) <- case parseArgs v of
                         Left err -> die err
                         Right (options, execmd) -> return (options, execmd)
  de <- doesDirectoryExist $ optTests options
  --fe <- doesFileExist $ exe
  --when (not fe) $ die $ "I cannot find an executable. I tried:" ++ exe
  when (not de) $ die $ "I cannot find a `" ++ optTests options ++ "' directory. Exiting"
  let (exename, exeargs) = fromMaybe ("", []) (uncons execmd)
  runTests options exename exeargs

showDiff :: Options -> [(DI,String)] -> String
showDiff options diff = unlines $ map (\(a,b) -> color options (colorDI a) (showDI a ++ b )) diff
 where showDI F = "+"
       showDI S = "-"
       showDI B = " "
       colorDI F = darkRed
       colorDI S = darkRed
       colorDI B = darkWhite
