{-# OPTIONS_GHC -Wno-unused-top-binds #-}
-- ============================================================================
-- Homework 02 — Functors, monads, IO, and small effects
-- ============================================================================

module HwEffects where

import Control.Monad (guard)
import Data.Char (toUpper)

-- ----------------------------------------------------------------------------
-- Sample data
-- ----------------------------------------------------------------------------

sampleNames :: [(Int, String)]
sampleNames =
  [ (1, "ada")
  , (2, "alan")
  ]

sampleEmails :: [(String, String)]
sampleEmails =
  [ ("ada", "ada@example.com")
  , ("alan", "alan@example.com")
  ]

samplePasswords :: [(String, String)]
samplePasswords =
  [ ("ada", "lambda")
  , ("alan", "turing")
  ]

-- ----------------------------------------------------------------------------
-- Problem 1 — Functor over Maybe
-- ----------------------------------------------------------------------------

cleanLine :: String -> String
cleanLine = map toUpper . unwords . words

cleanMaybeName :: Maybe String -> Maybe String
cleanMaybeName ms = fmap cleanLine ms

-- ----------------------------------------------------------------------------
-- Problem 2 — Functor over lists
-- ----------------------------------------------------------------------------

tagAll :: String -> [String] -> [String]
tagAll label items = fmap (\item -> label ++ ": " ++ item) items

-- ----------------------------------------------------------------------------
-- Problem 3 — Maybe as a small failure effect
-- ----------------------------------------------------------------------------

firstKnownEmail :: Int -> [(Int, String)] -> [(String, String)] -> Maybe String
firstKnownEmail uid names emails = do
  name  <- lookup uid names
  email <- lookup name emails
  return email

-- ----------------------------------------------------------------------------
-- Problem 4 — lists as nondeterminism
-- ----------------------------------------------------------------------------

pairsThatSum :: Int -> [Int] -> [(Int, Int)]
pairsThatSum target xs = do
  x <- xs
  y <- xs
  guard (x + y == target)
  return (x, y)

-- ----------------------------------------------------------------------------
-- Problem 5 — Either as an error-reporting effect
-- ----------------------------------------------------------------------------

data LoginError
  = MissingUser
  | BadPassword
  deriving (Eq, Show)

login :: String -> String -> [(String, String)] -> Either LoginError String
login username password table =
  case lookup username table of
    Nothing      -> Left MissingUser
    Just correct -> if password == correct
                      then Right ("Welcome, " ++ username ++ "!")
                      else Left BadPassword

-- ----------------------------------------------------------------------------
-- Problem 6 — IO shell around a pure core
-- ----------------------------------------------------------------------------

runCleanerOnce :: IO ()
runCleanerOnce = do
  line <- getLine
  putStrLn (cleanLine line)

-- ----------------------------------------------------------------------------
-- Problem 7 — recursive IO
-- ----------------------------------------------------------------------------

askNonEmpty :: String -> IO String
askNonEmpty prompt = do
  putStr prompt
  line <- getLine
  let cleaned = cleanLine line
  if null cleaned
    then do
      putStrLn "Please enter a non-empty answer."
      askNonEmpty prompt
    else return cleaned
