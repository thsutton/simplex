{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
module Lib where

import           Control.Monad.Except
import           Data.Array
import           Data.Function
import           Data.List
import           Data.Maybe
import           Data.Traversable
import           Data.Word

someFunc :: IO ()
someFunc = putStrLn "someFunc"

-- | Let's just pretend.
type Nat = Word16

-- * Problem descriptions

data Obj
  = Max [Rational]
  | Min [Rational]
  deriving (Eq, Ord, Show)

data Cons
  = LEq { coeffs :: [Rational], bound :: Rational }
  | GEq { coeffs :: [Rational], bound :: Rational }
  | Eq  { coeffs :: [Rational], bound :: Rational }
  deriving (Eq, Ord, Show)

needsSlack :: Cons -> Bool
needsSlack (Eq{}) = False
needsSlack _      = True

-- | Canonicalise objective function.
--
-- We take *minimise* to be the canonical representation of objective
-- functions in what follows.
objectify :: Obj -> [Rational]
objectify (Min o) = o
objectify (Max o) = negate `map` o

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
build obj constraints = initialise (objectify obj) (slack constraints)

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
  let (_, (rows, cols)) = bounds tab
  -- Let's find the pivot column, row, and element.
  colI <- findCol tab
  rowI <- findRow colI tab
  let div = tab ! (rowI, colI)
  replacement <- getRow rowI tab

  {-
   - Update the solution by replacing the variables selected:
   - For each (other) row, add
   -}
  tab <- updateRow tab ([0..cols] \\ [rowI]) (\current ->
    do
      let v = current ! colI
      return $ zipArray (-) current replacement
      )
  throwError (renderTableau tab)
  return (0, colI)
  where
    zipArray :: Ix i => (a -> b -> c) -> Array i a -> Array i b -> Array i c
    zipArray op as bs =
      let as' = assocs as
          bs' = assocs bs
      in array (bounds as) (zipWith (\(ix,a) (_,b) -> (ix,a `op` b)) as' bs')
    updateRow :: MonadError String m => Tableau -> [Nat] -> (Array Nat Rational -> m (Array Nat Rational)) -> m Tableau
    updateRow tab [] f     = return tab
    updateRow tab (r:rs) f = return tab
    findRow n tab = do
      let (_, (rows, cols)) = bounds tab
      col <- tail . elems <$> getCol n tab
      b <- tail . elems <$> getCol cols tab
      return . snd . minimum . filter (isJust . fst) $ zip (zipWith comp b col) [1..]
    comp :: Rational -> Rational -> Maybe Rational
    comp q r
      | r == 0 = Nothing
      | q / r > 0 = Just (q/r)
      | otherwise = Nothing
    flip (a,b) = (b,a)
    findCol tab = return . snd . minimum . filter (\(c,ix) -> c /= 0) . map flip $ assocs (costs tab)
    getCol :: MonadError String m => Nat -> Tableau -> m (Array Nat Rational)
    getCol n tab =
      let (_, (rows, cols)) = bounds tab
          col = map (\((r,_),v) -> (r,v)) . filter (\((r,c),v)-> c == n) $ assocs tab
      in return . array (0,rows) $ col

    getRow :: MonadError String m => Nat -> Tableau -> m (Array Nat Rational)
    getRow n tab =
      let (_, (rows, cols)) = bounds tab
          row = map (\((_,c),v) -> (c,v)) . filter (\((r,c),v) -> r == n) $ assocs tab
      in return . array (0,cols) $ row

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
