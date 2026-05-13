{-# OPTIONS_GHC -Wno-unused-top-binds #-}
-- ============================================================================
-- Homework — recursion, pattern matching, higher-order functions, Functor
-- ============================================================================

module HwFpBasics where

import Data.Char (toUpper)

-- ----------------------------------------------------------------------------
-- Problem 1 — pattern matching & recursion
-- ----------------------------------------------------------------------------

skip1 :: [a] -> [a]
skip1 []       = []
skip1 [x]      = [x]
skip1 (x:_:xs) = x : skip1 xs

-- ----------------------------------------------------------------------------
-- Problem 2 — recursion
-- ----------------------------------------------------------------------------

mySum :: [Int] -> Int
mySum []     = 0
mySum (x:xs) = x + mySum xs

-- ----------------------------------------------------------------------------
-- Problem 3 — higher-order functions
-- ----------------------------------------------------------------------------

countPasses :: [Int -> Bool] -> Int -> Int
countPasses preds x = length (filter (\p -> p x) preds)

-- ----------------------------------------------------------------------------
-- Problem 4 — Functor
-- ----------------------------------------------------------------------------

shoutInside :: Maybe String -> Maybe String
shoutInside ms = fmap (map toUpper) ms

-- ----------------------------------------------------------------------------
-- Problem 5 — merge sort
-- ----------------------------------------------------------------------------

merge :: Ord a => [a] -> [a] -> [a]
merge [] ys         = ys
merge xs []         = xs
merge (x:xs) (y:ys)
  | x <= y    = x : merge xs (y:ys)
  | otherwise = y : merge (x:xs) ys

mergeSort :: Ord a => [a] -> [a]
mergeSort []  = []
mergeSort [x] = [x]
mergeSort xs  =
  let mid        = length xs `div` 2
      (left, right) = splitAt mid xs
  in  merge (mergeSort left) (mergeSort right)
