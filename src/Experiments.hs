{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}

module Experiments where

import Classes (DerivGen, Generate (gen), Pick (..), generate)
import Control.Monad (forM_, replicateM, unless, when)
import Data.Hashable (Hashable)
import Data.IORef (modifyIORef, newIORef, readIORef)
import Data.List (group, groupBy, intercalate, minimumBy, sort, sortBy, tails)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Data.Ord (comparing)
import qualified Data.Set as Set
import qualified Data.Text as T
import Data.Text.Metrics (levenshtein)
import Data.Word (Word64)
import Examples
  ( Class (Class),
    HasStats (..),
    genAVLSkeleton,
    genExpr,
    genList,
    genT,
    genTree,
    hasType,
    hasTypeLcA,
    genProg,
    isAVL,
    isBST,
    isSorted,
    mergeFreqs,
    sumLeavesMul3,
    wellFormedAdtDecls,
    wellFormedType,
    genLcAType,
    genAdtDecls,
    nAdts,
  )
import FreeGen (FreeGen)
import GHC.Clock (getMonotonicTimeNSec)
import System.IO (IOMode (WriteMode), hClose, hPrint)
import qualified System.Timeout as Timeout
import qualified Test.QuickCheck as QC
import Text.Printf (printf)

----------------------------------------------------------------------------------------------------
-- Experimental Setup
----------------------------------------------------------------------------------------------------

-- | Defines the parameters of the experimental setup.
currentExperiments :: [Experiment]
currentExperiments = [lcaStlc]  --lcaStlc
  where
--    lcaSt = Experiment "LCAST" (genAdtDecls nAdts ) 40 wellFormedAdtDecls
    lcaStlc = Experiment "LCASTLC" genProg 40 hasTypeLcA
    -- bst = Experiment "BST" genTree 50 isBST
    -- sorted = Experiment "SORTED" genList 50 isSorted
    -- avl = Experiment "AVL" genAVLSkeleton 500 isAVL
    -- stlc = Experiment "STLC" genExpr 400 hasType
    -- div3 = Experiment "DIV3" genT 1 sumLeavesMul3

runningTime :: Seconds
runningTime = Seconds 5

makeCharts :: Bool
makeCharts = False

-- | Run experiments, outputting data to the `charts/` directory if `makeCharts` is `True`.
-- Also outputs summary data to stdout.
main :: IO ()
main = do
  print runningTime
  forM_ currentExperiments $ \(Experiment ename g samples valid) -> do
    putStrLn $ "[" ++ ename ++ "]"
    generateManyQC runningTime (fromJust <$> gen g) valid
      >>= processResults "QCRS" ename valid
    generateMany runningTime g valid samples
      >>= processResults "Grad" ename valid
  where
    processResults tag ename valid m = do
      unless (all valid (Map.keys m)) $ error "INVALID" -- Coherence check, for safety
      printStats tag m
      writeProgs ("charts/" ++ tag ++ "_" ++ ename ++ "_progs.dat") m
      when makeCharts $ do
        writeSizes ("charts/" ++ tag ++ "_" ++ ename ++ "_sizes.dat") m
        writeStamps ("charts/" ++ tag ++ "_" ++ ename ++ "_stamps.dat") m
        writeFreqs ("charts/" ++ tag ++ "_" ++ ename ++ "_freqs.dat") m

    printStats tag m = do
      putStr $ tag ++ ": "
      distStats <-
        mapM (distanceStats 5000)
          . Map.fromListWith (++)
          . map (\x -> (sizeFn x, [x]))
          . Map.keys
          $ m
      let sizeStats = stats . map sizeFn . Map.keys $ m
      subtreeStats <- uniqueSubtreeStats 100 . Map.keys $ m
      putStrLn
        ( "total="
            ++ show (Map.size m)
            ++ ",avg_size="
            ++ showStats sizeStats
            ++ ",avg_dist="
            ++ concatMap
              ( \(i, d) ->
                  show i ++ "," ++ showDouble d ++ "\n"
              )
              (Map.toList (fst <$> distStats))
            ++ ",subtree_uniqueness="
            ++ showStats subtreeStats
        )

    writeProgs fname m =
      writeFile fname (intercalate "\n" (map show (Map.keys m)))
    writeFreqs fname m =
      writeFile fname
        . unlines
        . map (intercalate "," . (\((Class c, n), f) -> [c, n, show f]))
        . Map.toList
        . mergeFreqs
        . map nodeFreqs
        . Map.keys
        $ m
    writeSizes fname m =
      let sizes = map sizeFn (Map.keys m)
       in writeFile fname . unlines . map (show . length) . group . sort $ sizes
    writeStamps fname m =
      let stamps@(earliest : _) = sort $ Map.elems m
       in writeFile
            fname
            ( unlines
                . map
                  (\t -> show ((t - earliest) `div` 1000000))
                $ stamps
            )

----------------------------------------------------------------------------------------------------
-- Outer Generation Loops
----------------------------------------------------------------------------------------------------

-- | Generate valid inputs for a given period of time using CGS.
generateMany ::
  ( DerivGen g,
    Eq a,
    Hashable a,
    Show a,
    Ord a
  ) =>
  Seconds ->
  g a ->
  (a -> Bool) ->
  Int ->
  IO (Map a Word64)
generateMany cutoff g valid n = do
  acc <- newIORef Map.empty
  timeout cutoff (aux acc)
  readIORef acc
  where
    aux acc =
      do
        vs <- generate g valid n
        forM_
          vs
          ( \x -> do
              t <- getMonotonicTimeNSec
              modifyIORef acc (insertIfAbsent x t)
          )
        aux acc

-- | Generate valid inputs for a given period of time using rejection sampling.
generateManyQC ::
  (Show a, Ord a) =>
  Seconds ->
  QC.Gen a ->
  (a -> Bool) ->
  IO (Map a Word64)
generateManyQC cutoff g valid = do
  acc <- newIORef Map.empty
  timeout cutoff (aux acc)
  readIORef acc
  where
    aux acc = do
      x <- QC.generate g
      if not (valid x)
        then aux acc
        else do
          t <- getMonotonicTimeNSec
          modifyIORef acc (insertIfAbsent x t)
          aux acc

----------------------------------------------------------------------------------------------------
-- SETUP
----------------------------------------------------------------------------------------------------

data Experiment where
  Experiment ::
    (Ord a, Show a, Hashable a, HasStats a) =>
    String ->
    FreeGen a ->
    Int ->
    (a -> Bool) ->
    Experiment

newtype Seconds = Seconds Int deriving (Eq)

instance Show Seconds where
  show (Seconds s) = show s ++ " seconds"

timeout :: Seconds -> IO () -> IO ()
timeout (Seconds n) = (() <$) . Timeout.timeout (n * 1_000_000)

showDouble :: Double -> String
showDouble = printf "%.3f"

showStats :: (Double, Double) -> String
showStats (avg, dev) = showDouble avg ++ " (" ++ showDouble dev ++ ")"

stats :: [Int] -> (Double, Double)
stats = stats' . map fromIntegral

stats' :: [Double] -> (Double, Double)
stats' xs = (avg, dev)
  where
    avg = sum xs / fromIntegral (length xs)
    dev = sqrt ((1.0 / n) * sum (map (\x -> (x - avg) ** 2) xs))
      where
        n = fromIntegral (length xs)

distanceStats :: HasStats a => Int -> [a] -> IO (Double, Double)
distanceStats samples (map (T.pack . ungenerate) -> xs) = stats <$> aux samples
  where
    getIdx = QC.generate (QC.choose (0, length xs - 1))
    aux 0 = pure []
    aux n = do
      x <- getIdx
      y <- getIdx
      (levenshtein (xs !! x) (xs !! y) :) <$> aux (n - 1)

uniqueSubtreeStats :: (Ord a, HasStats a) => Int -> [a] -> IO (Double, Double)
uniqueSubtreeStats samples xs = do
  measurements <- replicateM 30 $ do
    idxs <- replicateM samples getIdx
    pure . ((/ fromIntegral samples) . fromIntegral)
      . Set.size
      . Set.unions
      . map (subtrees . (xs !!))
      $ idxs
  pure (stats' measurements)
  where
    getIdx = QC.generate (QC.choose (0, length xs - 1))

insertIfAbsent :: Ord k => k -> v -> Map k v -> Map k v
insertIfAbsent k v m = if Map.member k m then m else Map.insert k v m
