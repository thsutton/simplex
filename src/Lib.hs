{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
module Lib where

import           Control.Monad.Except
import           Data.Array
import           Data.Function
import           Data.List
import           Data.Traversable
import           Data.Word

someFunc :: IO ()
someFunc = putStrLn "someFunc"

-- | Let's just pretend.
type Nat = Word16



-- * Problem descriptions

data Cons
  = LEq { coeffs :: [Rational], bound :: Rational }
  | GEq { coeffs :: [Rational], bound :: Rational }
  | Eq  { coeffs :: [Rational], bound :: Rational }
  deriving (Eq, Ord, Show)

needsSlack :: Cons -> Bool
needsSlack (Eq{}) = False
needsSlack _      = True

-- | Canonicalise constraints.
--
-- Add any missing zero coefficients and extend with slack variables.
slack :: [Cons] -> [([Rational], Rational)]
slack cons =
    let order = maximum $ map (length . coeffs) cons
        slacks = length $ filter needsSlack cons
    in snd (mapAccumL (row order slacks) 0 cons)
  where
    ident s n = take s ((take n (repeat 0)) ++ 1:zero s)
    zero s = take s (repeat 0)
    extend n as = as ++ (drop (length as) . take n $ repeat 0)
    row
      :: Int -- ^ Total coefficients
      -> Int -- ^ Total slack variables
      -> Int -- ^ Index of next slack variable
      -> Cons -> (Int, ([Rational], Rational))
    row order s i (Eq as b)  = (i  , (extend order as ++ zero s, b))
    row order s i (LEq as b) = (i+1, (extend order as ++ ident s i, b))
    row order s i (GEq as b) = (i+1, (extend order as ++ (map negate $ ident s i), b))

{-
build
  :: [Rational] -- ^ Objective function
  -> [Cons] -- ^ Constraints
  -> Either String Tableau
-}
build obj constraints = initialise obj (slack constraints)

-- * Tableaux

-- | We'll use NxN array of rational numbers as the tableaux.
type Tableau = Array (Nat, Nat) Rational

-- | Construct a tableau from an objective function and constraints.
--
-- We assume that the supplied values are such that they form a
-- canonical simplex tableau excepting that we will fill in any
-- "trailing" zero coefficients in the objective function and/or
-- constraint matrix.
initialise
  :: [Rational]  -- ^ Objective
  -> [([Rational], Rational)] -- ^ Constraints
  -> Either String Tableau
initialise obj cons =
  let order = fromIntegral $ max (length . shrink $ obj) (maximum $ map (length . shrink . fst) cons)
      rows  = fromIntegral $ length cons
      objective = index 0 $ row order (obj, 0) :: [((Nat,Nat), Rational)]
      matrix = concat $ zipWith index [1..] $ map (row order) cons :: [((Nat,Nat), Rational)]
  in Right $ array ((0,0), (rows, order)) (objective ++ matrix)
  where
    index :: Nat -> [(Nat, Rational)] -> [((Nat,Nat), Rational)]
    index n ms = map (\(m,r) -> ((n,m),r)) ms

shrink :: [Rational] -> [Rational]
shrink = reverse . dropWhile (==0) . reverse

row :: Nat -> ([Rational], Rational) -> [(Nat, Rational)]
row n (coeff, bound) =
  let zeros = drop (length coeff) $ take (fromIntegral n) (repeat 0)
  in zip [0..] (coeff ++ zeros ++ [bound])

type Point = Array Nat Rational

-- | We solve a 'Tableau' yielding either an error or a 'Point'.
step :: Tableau -> Either String Tableau
step tab = do
  col <- selectPivot tab
  Left (show col ++ "\n" ++ renderTableau tab)
  Right tab

-- | Select a column to pivot.
--
-- We chose the most
selectPivot :: MonadError String m => Tableau -> m (Nat,Nat)
selectPivot tab = do
  let (rows, cols) = bounds tab
  let (cost, col) = maximum . map flip $ assocs (costs tab)
  return (0,col)
  where
    flip (a,b) = (b,a)

costs :: Tableau -> Array Nat Rational
costs tab =
  let ((_,_), (rows, cols)) = bounds tab
      cs = filter check (assocs tab) :: [((Nat,Nat),Rational)]
  in array (0, cols) (map (\((a,b),c) -> (b,c)) cs)
  where
    check ((a,b),c) = a == 0

-- | Render a 'Tableau'.
--
-- This is truly awful.
renderTableau :: Tableau -> String
renderTableau tab =
  let rows = map (map snd) $ groupBy ((==) `on` (fst . fst)) (assocs tab)
      widths = maxes $ map (map (length . show)) rows
  in unlines (map (concat . intersperse "    " . zipWith pad widths . map show) rows)
  where
    pad n s =
      let l = length s
      in (take (n - l) $ repeat ' ') ++ s
    safeSplit :: [a] -> ([a], [a])
    safeSplit []    = ([], [])
    safeSplit (h:r) = ([h], r)
    maxes :: [[Int]] -> [Int]
    maxes ls =
      let lol = map safeSplit ls
          heads = concatMap fst lol
          tails = map snd lol
      in maximum heads : maxes tails
