{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wall #-}

module Examples where

import Classes (Pick (pick))
import Control.Arrow (first, second)
import Control.Monad (guard, zipWithM)
import Control.Monad.Reader (ReaderT (runReaderT), ask, local)
import Control.Monad.Trans (lift)
import Data.Hashable (Hashable (..))
import Data.List (nub, sort, intercalate)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (isJust)
import Data.Set (Set)
import qualified Data.Set as Set
import FreeGen (FreeGen)
import GHC.Generics (Generic)
import Debug.Trace (traceStack)

----------------------------------------------------------------------------------------------------
-- SETUP
----------------------------------------------------------------------------------------------------

class HasStats a where
  sizeFn :: a -> Int
  nodeFreqs :: a -> Map (Class, String) Int
  ungenerate :: a -> String
  subtrees :: a -> Set a

newtype Class = Class String deriving (Ord, Eq, Show)

unit :: Class -> String -> Map (Class, String) Int
unit c = (`Map.singleton` 1) . (c,)

mergeFreqs :: Ord k => [Map k Int] -> Map k Int
mergeFreqs = Map.unionsWith (+)

normClasses :: Map (Class, String) Int -> Map (Class, String) Double
normClasses m = Map.mapWithKey (\(c, _) a -> fromIntegral a / fromIntegral (classSum c)) m
  where
    classSum c = sum . Map.elems . Map.filterWithKey (\(c', _) _ -> c == c') $ m

----------------------------------------------------------------------------------------------------
-- Binary Search Trees
----------------------------------------------------------------------------------------------------

data Tree a = Node a (Tree a) (Tree a) | Leaf
  deriving (Eq, Ord, Show, Read, Generic, Hashable)

isBST :: Ord a => Tree a -> Bool
isBST Leaf = True
isBST (Node x l r) =
  all (< x) (treeToList l)
    && all (> x) (treeToList r)
    && isBST l
    && isBST r

treeToList :: Tree a -> [a]
treeToList t = aux t []
  where
    aux Leaf = id
    aux (Node x l r) = aux l . (x :) . aux r

genTree :: (Applicative g, Pick g) => g (Tree Int)
genTree = aux (5 :: Int)
  where
    aux 0 = pure Leaf
    aux n =
      pick
        [ ( 1,
            "l",
            pure Leaf
          ),
          ( 1,
            "n",
            Node <$> genInt <*> aux (n - 1) <*> aux (n - 1)
          )
        ]
    genInt = pick [(1, show n, pure n) | n <- [0 .. 9]]

genBST :: (Int, Int) -> FreeGen (Tree Int)
genBST (lo, hi) | lo > hi = pure Leaf
genBST (lo, hi) = do
  c <- pick [(1, "l", pure False), (1, "n", pure True)]
  if c
    then pure Leaf
    else do
      x <- pick [(1, show n, pure n) | n <- [lo .. hi]]
      l <- genBST (lo, x - 1)
      r <- genBST (x + 1, hi)
      pure (Node x l r)

instance HasStats (Tree Int) where
  sizeFn Leaf = 0
  sizeFn (Node _ l r) = 1 + sizeFn l + sizeFn r

  nodeFreqs (Node x l r) =
    Map.unionsWith
      (+)
      [ unit (Class "value") (show x),
        unit (Class "structure") "Node",
        nodeFreqs l,
        nodeFreqs r
      ]
  nodeFreqs Leaf = unit (Class "structure") "Leaf"

  ungenerate (Node x l r) = 'n' : (['0' .. '9'] !! x) : ungenerate l ++ ungenerate r
  ungenerate Leaf = "l"

  subtrees Leaf = Set.singleton Leaf
  subtrees n@(Node _ l r) = Set.unions [Set.singleton n, subtrees l, subtrees r]

sliftA2 :: (Ord a, Ord b, Ord c) => (a -> b -> c) -> Set a -> Set b -> Set c
sliftA2 f a b = Set.map (uncurry f) (Set.cartesianProduct a b)

splits :: Int -> [(Int, Int)]
splits = nub . sort . aux
  where
    aux 0 = [(0, 0)]
    aux k =
      let ss = aux (k - 1)
       in map (first (+ 1)) ss ++ map (second (+ 1)) ss

----------------------------------------------------------------------------------------------------
-- Sorted Lists
----------------------------------------------------------------------------------------------------

genList :: (Applicative g, Pick g) => g [Int]
genList = aux (20 :: Int)
  where
    aux 0 = pure []
    aux n =
      pick
        [ (1, "n", pure []),
          (1, "c", (:) <$> genInt <*> aux (n - 1))
        ]
    genInt = pick [(1, show n, pure n) | n <- [0 .. 9]]

isSorted :: [Int] -> Bool
isSorted [] = True
isSorted [_] = True
isSorted (x : y : xs) = x <= y && isSorted (y : xs)

instance HasStats [Int] where
  sizeFn = length

  nodeFreqs (x : xs) =
    Map.unionsWith
      (+)
      [ unit (Class "value") (show x),
        unit (Class "structure") "Cons",
        nodeFreqs xs
      ]
  nodeFreqs [] = unit (Class "structure") "Nil"

  ungenerate = map (['0' .. '9'] !!)

  subtrees [] = Set.singleton []
  subtrees l@(_ : xs) = Set.insert l (subtrees xs)

----------------------------------------------------------------------------------------------------
-- Trees with Leaves That Multiply to Three
----------------------------------------------------------------------------------------------------

data T = L Int | N T T
  deriving (Eq, Ord, Show, Read, Generic, Hashable)

foldT :: (Int -> a) -> (a -> a -> a) -> T -> a
foldT b _ (L x) = b x
foldT b n (N l r) = n (foldT b n l) (foldT b n r)

sumLeavesMul3 :: T -> Bool
sumLeavesMul3 !t = foldT (`mod` 3) (\x y -> (x + y) `mod` 3) t == 0

toList :: T -> [Int]
toList = foldT (: []) (++)

genT :: (Applicative g, Pick g) => g T
genT = aux (5 :: Int)
  where
    aux 0 = L <$> genInt
    aux n =
      pick
        [ ( 1,
            "l",
            L <$> genInt
          ),
          ( 1,
            "n",
            N <$> aux (n - 1) <*> aux (n - 1)
          )
        ]
    genInt = pick [(1, show n, pure n) | n <- [0 .. 9]]

instance HasStats T where
  sizeFn = length . toList
  nodeFreqs (N l r) =
    Map.unionsWith
      (+)
      [ unit (Class "structure") "Node",
        nodeFreqs l,
        nodeFreqs r
      ]
  nodeFreqs (L x) =
    Map.unionsWith
      (+)
      [ unit (Class "value") (show x),
        unit (Class "structure") "Leaf"
      ]

  ungenerate (L x) = "l" ++ show x
  ungenerate (N l r) = "n" ++ ungenerate l ++ ungenerate r

  subtrees t@(L _) = Set.singleton t
  subtrees t@(N l r) = Set.unions [Set.singleton t, subtrees l, subtrees r]

----------------------------------------------------------------------------------------------------
-- AVL Trees
----------------------------------------------------------------------------------------------------

data AVL a = AVLNode a (AVL a) (AVL a) Int | AVLLeaf
  deriving (Eq, Ord, Show, Read, Generic, Hashable)

getHeight :: AVL a -> Int
getHeight AVLLeaf = 0
getHeight (AVLNode _ _ _ h) = h

avlNode :: a -> AVL a -> AVL a -> AVL a
avlNode x l r = AVLNode x l r (1 + max (getHeight l) (getHeight r))

isAVL :: Ord a => AVL a -> Bool
isAVL tree = avlIsBST tree && avlHeightInv tree && avlBalanceInv tree
  where
    avlIsBST AVLLeaf = True
    avlIsBST (AVLNode x l r _) =
      all (< x) (avlToList l)
        && all (> x) (avlToList r)
        && avlIsBST l
        && avlIsBST r

    avlHeightInv AVLLeaf = True
    avlHeightInv (AVLNode _ l r h) =
      h == 1 + max (getHeight l) (getHeight r)
        && avlHeightInv l
        && avlHeightInv r

    avlBalanceInv AVLLeaf = True
    avlBalanceInv (AVLNode _ l r _) =
      abs (getHeight l - getHeight r) <= 1
        && avlBalanceInv l
        && avlBalanceInv r

avlToList :: AVL a -> [a]
avlToList t = aux t []
  where
    aux AVLLeaf = id
    aux (AVLNode x l r _) = aux l . (x :) . aux r

genAVLSkeleton :: forall g. (Applicative g, Pick g) => g (AVL Int)
genAVLSkeleton = aux (5 :: Int)
  where
    aux :: Int -> g (AVL Int)
    aux 0 = pure AVLLeaf
    aux n =
      pick
        [ ( 1,
            "l",
            pure AVLLeaf
          ),
          ( 1,
            "n",
            do
              h <- genInt
              x <- genInt
              l <- aux (n - 1)
              r <- aux (n - 1)
              pure (AVLNode x l r h)
          )
        ]
    genInt = pick [(1, show n, pure n) | n <- [0 .. 9]]

genAVLSkeletonCache :: forall g. (Applicative g, Pick g) => g (AVL Int)
genAVLSkeletonCache = aux (5 :: Int)
  where
    aux :: Int -> g (AVL Int)
    aux 0 = pure AVLLeaf
    aux n =
      pick
        [ ( 1,
            "l",
            pure AVLLeaf
          ),
          ( 1,
            "n",
            do
              x <- genInt
              l <- aux (n - 1)
              r <- aux (n - 1)
              pure (AVLNode x l r (1 + max (getHeight l) (getHeight r)))
          )
        ]
    genInt = pick [(1, show n, pure n) | n <- [0 .. 9]]

instance HasStats (AVL Int) where
  sizeFn AVLLeaf = 0
  sizeFn (AVLNode _ l r _) = 1 + sizeFn l + sizeFn r

  nodeFreqs (AVLNode x l r _) =
    Map.unionsWith
      (+)
      [ unit (Class "value") (show x),
        unit (Class "structure") "Node",
        nodeFreqs l,
        nodeFreqs r
      ]
  nodeFreqs AVLLeaf = unit (Class "structure") "Leaf"

  ungenerate (AVLNode x l r h) =
    'n' : (['a', 'b' ..] !! x) : ungenerate l ++ ungenerate r ++ [['0' .. '9'] !! h]
  ungenerate AVLLeaf = "l"

  subtrees AVLLeaf = Set.singleton AVLLeaf
  subtrees n@(AVLNode _ l r _) = Set.unions [Set.singleton n, subtrees l, subtrees r]

----------------------------------------------------------------------------------------------------
-- Red-Black Trees
----------------------------------------------------------------------------------------------------

newtype RBT a = RBT (RBTree a)
  deriving (Eq, Ord, Show, Read, Generic, Hashable)

data Color = Red | Black
  deriving (Eq, Ord, Show, Read, Generic, Hashable)

data RBTree a = RBNode Color a (RBTree a) (RBTree a) | RBLeaf
  deriving (Eq, Ord, Show, Read, Generic, Hashable)

getColor :: RBTree a -> Color
getColor RBLeaf = Black
getColor (RBNode c _ _ _) = c

blackHeight :: RBTree a -> Int
blackHeight RBLeaf = 1
blackHeight (RBNode c _ l r) = (if c == Black then 1 else 0) + max (blackHeight l) (blackHeight r)

isRBT :: Ord a => RBT a -> Bool
isRBT (RBT tree) = rbtIsBST tree && rnbcInv tree && blackHeightInv tree
  where
    rbtIsBST RBLeaf = True
    rbtIsBST (RBNode _ x l r) =
      all (< x) (rbtToList l)
        && all (> x) (rbtToList r)
        && rbtIsBST l
        && rbtIsBST r

    rnbcInv RBLeaf = True
    rnbcInv (RBNode c _ l r) =
      (c == Black || getColor l == Black && getColor r == Black) && rnbcInv l && rnbcInv r

    blackHeightInv RBLeaf = True
    blackHeightInv (RBNode _ _ l r) =
      (blackHeight l == blackHeight r) && blackHeightInv l && blackHeightInv r

rbtToList :: RBTree a -> [a]
rbtToList t = aux t []
  where
    aux RBLeaf = id
    aux (RBNode _ x l r) = aux l . (x :) . aux r

genRBTSkeleton :: forall g. (Applicative g, Pick g) => g (RBT Int)
genRBTSkeleton = RBT <$> aux (5 :: Int)
  where
    aux :: Int -> g (RBTree Int)
    aux 0 = pure RBLeaf
    aux n =
      pick
        [ ( 1,
            "l",
            pure RBLeaf
          ),
          ( 1,
            "n",
            RBNode
              <$> pick [(1, "r", pure Red), (1, "b", pure Black)]
              <*> genInt
              <*> aux (n - 1)
              <*> aux (n - 1)
          )
        ]
    genInt = pick [(1, show n, pure n) | n <- [0 .. 9]]

instance HasStats (RBT Int) where
  sizeFn (RBT t) = aux t
    where
      aux RBLeaf = 0
      aux (RBNode _ _ l r) = 1 + aux l + aux r

  nodeFreqs (RBT t) = aux t
    where
      aux (RBNode _ x l r) =
        Map.unionsWith
          (+)
          [ unit (Class "value") (show x),
            unit (Class "structure") "Node",
            aux l,
            aux r
          ]
      aux RBLeaf = unit (Class "structure") "Leaf"

  ungenerate (RBT t) = aux t
    where
      aux (RBNode c x l r) =
        (case c of Red -> 'r'; Black -> 'b') : 'n' : (['a', 'b' ..] !! x) : aux l ++ aux r
      aux RBLeaf = "l"

  subtrees = undefined

----------------------------------------------------------------------------------------------------
-- STLC Expressions
----------------------------------------------------------------------------------------------------

data Type = TInt | Fun Type Type
  deriving (Show, Eq, Ord, Generic, Hashable)

data Expr = Int Int | Plus Expr Expr | Lam Type Expr | Var Int | App Expr Expr
  deriving (Show, Eq, Ord, Generic, Hashable)

typeOf :: Expr -> Maybe Type
typeOf expr = runReaderT (aux expr) []
  where
    aux :: Expr -> ReaderT [Type] Maybe Type
    aux (Int _) = return TInt
    aux (Plus e1 e2) = do
      TInt <- aux e1
      TInt <- aux e2
      return TInt
    aux (Lam t e) = do
      t' <- local (t :) (aux e)
      return (Fun t t')
    aux (App e1 e2) = do
      (Fun t1 t2) <- aux e1
      t1' <- aux e2
      guard (t1 == t1')
      return t2
    aux (Var n) = do
      ctx <- ask
      if length ctx <= n then lift Nothing else return (ctx !! n)

hasType :: Expr -> Bool
hasType = isJust . typeOf

genExpr :: (Applicative g, Pick g) => g Expr
genExpr = aux (5 :: Int)
  where
    aux 0 = pick [(1, "i", Int <$> genInt), (1, "v", Var <$> genVar)]
    aux n =
      pick
        [ (1, "i", pick [(1, show i, pure (Int i)) | i <- [0 .. 3]]),
          (1, "+", Plus <$> aux (n - 1) <*> aux (n - 1)),
          (1, "λ", Lam <$> genType (2 :: Int) <*> aux (n - 1)),
          (1, "@", App <$> aux (n - 1) <*> aux (n - 1)),
          (1, "v", Var <$> genVar)
        ]

    genInt = pick [(1, show n, pure n) | n <- [0 .. 3]]
    genVar = pick [(1, ["x", "y", "z"] !! v, pure v) | v <- [0, 1, 2]]
    genType 0 = pure TInt
    genType n =
      pick
        [ (1, "ℕ", pure TInt),
          (1, "→", Fun <$> genType (n - 1) <*> genType (n - 1))
        ]

genScopedExpr :: (Applicative g, Pick g) => g Expr
genScopedExpr = aux (5 :: Int) (-1)
  where
    aux 0 ctx = pick [(1, "i", Int <$> genInt), (1, "v", Var <$> genVar ctx)]
    aux n ctx =
      pick
        [ (1, "i", pick [(1, show i, pure (Int i)) | i <- [0 .. 3]]),
          (1, "+", Plus <$> aux (n - 1) ctx <*> aux (n - 1) ctx),
          (1, "λ", Lam <$> genType (2 :: Int) <*> aux (n - 1) (ctx + 1)),
          (1, "@", App <$> aux (n - 1) ctx <*> aux (n - 1) ctx),
          (1, "v", Var <$> genVar ctx)
        ]

    genInt = pick [(1, show n, pure n) | n <- [0 .. 3]]
    genVar ctx = pick [(1, ["x", "y", "z"] !! v, pure v) | v <- [0 .. ctx]]
    genType 0 = pure TInt
    genType n =
      pick
        [ (1, "ℕ", pure TInt),
          (1, "→", Fun <$> genType (n - 1) <*> genType (n - 1))
        ]

instance HasStats Expr where
  sizeFn (Int _) = 1
  sizeFn (Plus e1 e2) = 1 + sizeFn e1 + sizeFn e2
  sizeFn (Lam _ e) = 1 + sizeFn e
  sizeFn (Var _) = 1
  sizeFn (App e1 e2) = 1 + sizeFn e1 + sizeFn e2
  nodeFreqs (Int i) = unit (Class "structure") ("Lit_" ++ show i)
  nodeFreqs (Plus x y) =
    mergeFreqs
      [unit (Class "structure") "Plus", nodeFreqs x, nodeFreqs y]
  nodeFreqs (Lam t x) =
    mergeFreqs
      [unit (Class "structure") "Lam", typeFreqs t, nodeFreqs x]
    where
      typeFreqs TInt = unit (Class "type") "TInt"
      typeFreqs (Fun t1 t2) =
        mergeFreqs
          [unit (Class "type") "Fun", typeFreqs t1, typeFreqs t2]
  nodeFreqs (Var i) = unit (Class "structure") ("Var_" ++ show i)
  nodeFreqs (App x y) =
    mergeFreqs
      [unit (Class "structure") "App", nodeFreqs x, nodeFreqs y]
  ungenerate (Int i) = [['0' .. '9'] !! i]
  ungenerate (Plus x y) = 'p' : ungenerate x ++ ungenerate y
  ungenerate (Lam t x) =
    'l' : ungenerateTy t ++ ungenerate x
    where
      ungenerateTy TInt = "i"
      ungenerateTy (Fun t1 t2) = 'f' : ungenerateTy t1 ++ ungenerateTy t2
  ungenerate (Var i) = ["x", "y", "z"] !! i
  ungenerate (App x y) = 'a' : ungenerate x ++ ungenerate y

  subtrees n@(Int _) = Set.singleton n
  subtrees n@(Plus x y) = Set.unions [Set.singleton n, subtrees x, subtrees y]
  subtrees n@(Lam _ x) = Set.insert n (subtrees x)
  subtrees n@(Var _) = Set.singleton n
  subtrees n@(App x y) = Set.unions [Set.singleton n, subtrees x, subtrees y]

----------------------------------------------------------------------------------------------------
-- STLC+ADTs Programs
----------------------------------------------------------------------------------------------------

data LcAType = LcATInt | LcAFun LcAType LcAType | LcATAdt Int
  deriving (Eq, Ord, Generic, Hashable)

-- We index constructor tags by their position in a the enclosing ADT
-- declarations. For example: in the declaration [[Int,Fun Int
-- Int],[Int]], the first sublist represents a data declaration with
-- two constructors and thus two constructor tags, indexed by 0 and 1,
-- and the second sublist a data declaration with one constructor with
-- one tag, indexed by 2. This way, each constructor tag is easily
-- associated with its enclosing ADT declaration.
type AdtConstr = [LcAType]
type AdtDecl = [AdtConstr]
type AdtDecls = [AdtDecl]

data LcAExpr = LcAInt Int | LcAPlus LcAExpr LcAExpr | LcALam LcAType LcAExpr | LcAVar Int | LcAApp LcAExpr LcAExpr
  | LcAConstr Int [LcAExpr] | LcACase LcAExpr [LcAExpr]
  deriving (Eq, Ord, Generic, Hashable)

type LcAProg = (AdtDecls, LcAExpr)

checkIx :: String -> Int -> Int -> a -> a
checkIx s i n x
  | i < 0 || i >= n = traceStack ("out of bounds " ++ show i ++ " " ++ show n ++ " " ++ s) x
  | otherwise = x

-- String output
-- -------------
-- (in S-expression format)

showSexprConstr :: String -> [String] -> String
showSexprConstr c [] = "(" ++ c ++ ")"
showSexprConstr c [c'] = "(" ++ c ++ " " ++ c' ++ ")"
showSexprConstr c cs = "(" ++ c ++ " " ++ intercalate " " cs ++ ")"

showSexprList :: [String] -> String
showSexprList [] = "()"
showSexprList [c] = "(" ++ c ++ ")"
showSexprList cs = "(" ++ intercalate " " cs ++ ")"

varStrs :: [String]
varStrs = ["x", "y", "z"] ++ ["x" ++ show n | n <- [1..]]

adtDeclStrs :: [String]
adtDeclStrs = ["d" ++ show n | n <- [1..]]

showLcABinder :: Int -> LcAType -> String
showLcABinder ctx t = "(" ++ v ++ " " ++ show t ++ ")"
  where
    v | ctx < 0 = "<bogus binder>"
      | otherwise = varStrs !! ctx

showLcAExpr :: AdtDecls -> LcAExpr -> String
showLcAExpr decls = aux 0
  where
    constrTbl = mkConstrTbl decls
    aux _ (LcAInt x) = show x
    aux ctx (LcAPlus e1 e2) = showSexprConstr "+" (map (aux ctx) [e1, e2])
    aux ctx (LcALam t e) = showSexprConstr "λ" [showLcABinder ctx t, aux (ctx + 1) e]
    aux ctx (LcAVar v) | ctx <= 0 = "<bogus variable use site>"
                       | otherwise = varStrs !! (ctx - v - 1)
    aux ctx (LcAApp e1 e2) = showSexprList (map (aux ctx) [e1, e2])
    aux ctx (LcAConstr c es) =
      case adtOfConstrIx c constrTbl of
        Nothing -> "<bogus>"
        Just i -> showSexprConstr ("K-" ++ show i ++ "-" ++ show j) (map (aux ctx) es)
          where j = c - sum [x | x <- take i constrTbl]
    aux ctx (LcACase e es) = showSexprConstr "case" ((aux ctx e) : (map (aux ctx) (e : es))) -- todo: need to increment d based on arity of each pattern match

-- instance Show LcAExpr where
--   show e = showLcAExpr e

instance Show LcAType where
  show LcATInt = showSexprConstr "int 32" []
  show (LcAFun t1 t2) = showSexprConstr "→" [show t1, show t2]
  show (LcATAdt i) = adtDeclStrs !! i

showConstr :: Int -> Int -> AdtConstr -> String
showConstr i j c = showSexprConstr ("K-" ++ show i ++ "-" ++ show j) (map show c)

showDecl :: Int -> AdtDecl -> String
showDecl i d = showSexprConstr (adtDeclStrs !! i) (zipWith (showConstr i) [0 .. (length d - 1)] d)

showAdtDecls :: AdtDecls -> String
showAdtDecls ds = showSexprList (zipWith showDecl [0 .. (length ds - 1)] ds)
  
-- instance {-# OVERLAPPING #-} Show AdtDecls where
--   show ds = showSexprList (zipWith showDecl [0 .. (length ds - 1)] ds)

instance {-# OVERLAPPING #-} Show LcAProg where
  show (decls, e) = showSexprList [showAdtDecls decls, "\n\t", showLcAExpr decls e]

-- https://hackage.haskell.org/package/base-4.17.0.0/docs/GHC-Stack.html#t:HasCallStack

validIx :: Int -> Int -> Bool
validIx i n = (i >= 0) && (i < n)

-- n: nb of adt decls
wellFormedType :: Int -> LcAType -> Bool
wellFormedType n (LcATAdt adt) = validIx adt n
wellFormedType _ _ = True

wellFormedAdtConstr :: Int -> AdtConstr -> Bool
wellFormedAdtConstr n = all (wellFormedType n)

wellFormedAdtDecl :: Int -> AdtDecl -> Bool
wellFormedAdtDecl n = all (wellFormedAdtConstr n)

wellFormedAdtDecls :: AdtDecls -> Bool
wellFormedAdtDecls decls = all (wellFormedAdtDecl (length decls)) decls

type ConstrTbl = [Int] -- nb constrs per decl; used to speed up searches for the adt of a given constructor index

mkConstrTbl :: AdtDecls -> ConstrTbl
mkConstrTbl = tail . scanl (+) 0 . map length

-- later: maybe use binary search
search :: (Ord a) => a -> [a] -> Maybe Int
search n = aux 0
  where
    aux _ [] = Nothing
    aux i (x : xs) = if x > n then Just i else aux (i + 1) xs

adtOfConstrIx :: Int -> ConstrTbl -> Maybe Int
adtOfConstrIx = search

constrOfIx :: Int -> AdtDecls -> AdtConstr
constrOfIx c decls = checkIx "3" c (length ds) (ds !! c)
  where ds = concat decls

exDcl1 :: AdtDecl
exDcl1 = [[LcATAdt 0,LcAFun LcATInt LcATInt],[LcATInt],[LcATAdt 1]]

exDcl2 :: AdtDecl
exDcl2 = [[LcATAdt 0],[LcATInt]]

exDcls1 :: AdtDecls
exDcls1 = [exDcl1,exDcl2]

wfTbl1 :: Bool
wfTbl1 = wellFormedAdtDecls exDcls1 -- todo: assert that it's true

exConstrTbl1 :: ConstrTbl
exConstrTbl1 = mkConstrTbl exDcls1

hasTypeLcA ::  LcAProg -> Bool
hasTypeLcA = isJust . typeOfLcAProg

typeOfLcAProg :: LcAProg -> Maybe LcAType
typeOfLcAProg (decls, expr) = typeOfLcA decls expr

typeOfLcA :: AdtDecls -> LcAExpr -> Maybe LcAType
typeOfLcA decls expr = runReaderT (aux expr) []
  where
    constrTbl = mkConstrTbl decls
    aux :: LcAExpr -> ReaderT [LcAType] Maybe LcAType
    aux (LcAInt _) = return LcATInt
    aux (LcAPlus e1 e2) = do
      LcATInt <- aux e1
      LcATInt <- aux e2
      return LcATInt
    aux (LcALam t e) = do
      t' <- local (t :) (aux e)
      return (LcAFun t t')
    aux (LcAApp e1 e2) = do
      (LcAFun t1 t2) <- aux e1
      t1' <- aux e2
      guard (t1 == t1')
      return t2
    aux (LcAVar n) = do
      ctx <- ask
      guard (n >= 0)
      checkIx "4" n 3 (if length ctx <= n then lift Nothing else return (ctx !! n))
    aux (LcAConstr c es) = do
      (Just adt) <- return (adtOfConstrIx c constrTbl)
      let ts = constrOfIx c decls
      ts' <- mapM aux es
      guard (ts == ts')
      return (LcATAdt adt)
    aux (LcACase e es) = do
      (LcATAdt adt) <- aux e
      let cs = checkIx "100" adt (length decls) (decls !! adt)
      guard (length cs == length es)
      ts <- zipWithM auxPat cs es
      guard (not (null ts))
      let t1 = head ts
      guard (all (\ b -> b) (map (t1 ==) ts))
      return t1
    auxPat :: AdtConstr -> LcAExpr -> ReaderT [LcAType] Maybe LcAType
    auxPat c e = do
      t <- local (c ++) (aux e)
      return t

exExpr1 :: LcAExpr
exExpr1 = LcAConstr 4 [LcAInt 123]

--typeOfLcA exDcls1 exExpr1

exExpr2 :: LcAExpr
exExpr2 = LcAConstr 2 [exExpr1]

nAdts :: Int
nAdts = 2

genLcAType :: forall g. (Monad g, Pick g) => Int -> g LcAType
genLcAType 0 = pure LcATInt
genLcAType n =
  pick
    [ (1, "ℕ", pure LcATInt),
      (1, "→", LcAFun <$> genLcAType (n - 1) <*> genLcAType (n - 1)),
      (1, "D", LcATAdt <$> genAdt)
    ]

genAdt :: forall g. (Monad g, Pick g) => g Int
genAdt = pick [(1, show n, pure n) | n <- [0 .. (nAdts - 1)]]
                   
genAdtDecls :: forall g. (Monad g, Pick g) => Int -> g AdtDecls
genAdtDecls 0 = pure []
genAdtDecls n = (:) <$> genAdtDecl (5 :: Int) <*> genAdtDecls (n - 1)
  
genAdtDecl :: forall g. (Monad g, Pick g) => Int -> g AdtDecl
genAdtDecl 0 = (:) <$> genAdtConstr (5 :: Int) <*> pure []
genAdtDecl n = pick [(1, "Dn", genAdtDecl 0),
                     (1, "Dc", (:) <$> genAdtConstr (5 :: Int) <*> genAdtDecl (n - 1))]

genAdtConstr :: forall g. (Monad g, Pick g) => Int -> g AdtConstr
genAdtConstr 0 = pure []
genAdtConstr n = pick [(1, "Cn", pure []),
                       (1, "Cc", (:) <$> genLcAType (2 :: Int) <*> genAdtConstr (n - 1))]

genLcAExpr :: forall g. (Monad g, Pick g) => AdtDecls -> g LcAExpr
genLcAExpr decls = aux (5 :: Int)
  where
    aux 0 = pick [(1, "i", LcAInt <$> genInt), (1, "v", LcAVar <$> genVar)]
    aux n =
      pick
        [ (1, "i", pick [(1, show i, pure (LcAInt i)) | i <- [0 .. 3]]),
          (1, "+", LcAPlus <$> aux (n - 1) <*> aux (n - 1)),
          (1, "λ", LcALam <$> genLcAType (2 :: Int) <*> aux (n - 1)),
          (1, "@", LcAApp <$> aux (n - 1) <*> aux (n - 1)),
          (1, "v", LcAVar <$> genVar),
          (1, "K", LcAConstr <$> genConstr <*> genExprs)
        ]
    genInt = pick [(1, show n, pure n) | n <- [0 .. 3]]
    genVar = pick [(1, varStrs !! v, pure v) | v <- [0, 1, 2]]
    genConstr = pick [(1, show c, pure c) | c <- [0 .. (nConstrs - 1)]]
    genExprs = do
      n <- genInt
      genExprs' n
    genExprs' 0 = pure []
    genExprs' n = pick [(1, "En", pure []),
                        (1, "Ec", (:) <$> aux (5 :: Int) <*> genExprs' (n - 1))]
    constrTbl = mkConstrTbl decls
    nConstrs = sum constrTbl

genProg :: forall g. (Monad g, Pick g) => g LcAProg
genProg = do
  adtDecls <- genAdtDecls nAdts
  expr <- genLcAExpr adtDecls
  pure (adtDecls, expr)

instance HasStats LcAProg where
  sizeFn (ds, e) = sizeFn ds + sizeFn e
  nodeFreqs (ds, e) =
    mergeFreqs [unit (Class "prog") "Prog", nodeFreqs ds, nodeFreqs e]
  ungenerate (ds, e) = ungenerate ds ++ ungenerate e
  subtrees (ds, e) = Set.cartesianProduct (subtrees ds) (subtrees e)

instance HasStats AdtDecls where
  sizeFn = sum . map sizeFn
  nodeFreqs ds = mergeFreqs ([unit (Class "decls") "Decls"] ++ map nodeFreqs ds)
  ungenerate = concat . map ungenerate
  subtrees ds = Set.singleton (filter (not . null) ds)
  
instance HasStats AdtDecl where
  sizeFn = sum . map sizeFn
  nodeFreqs ds = mergeFreqs ([unit (Class "constrs") "Constrs"] ++ map nodeFreqs ds)
  ungenerate = concat . map ungenerate
  subtrees ds = Set.singleton (filter (not . null) ds)

instance HasStats AdtConstr where
  sizeFn = sum . map sizeFn
  nodeFreqs ds = mergeFreqs ([unit (Class "fields") "Fields"] ++ map nodeFreqs ds)
  ungenerate = concat . map ungenerate
  subtrees fs = Set.singleton fs

instance HasStats LcAType where
  sizeFn (LcAFun t1 t2) = 1 + sizeFn t1 + sizeFn t2
  sizeFn _ = 1
  nodeFreqs LcATInt = unit (Class "type") "TInt"
  nodeFreqs (LcAFun t1 t2) =
    mergeFreqs [unit (Class "type") "Fun", nodeFreqs t1, nodeFreqs t2]
  nodeFreqs (LcATAdt i) = unit (Class "type") ("TAdt" ++ show i)
  ungenerate LcATInt = "i"
  ungenerate (LcAFun t1 t2) = 'f' : ungenerate t1 ++ ungenerate t2
  ungenerate (LcATAdt i) = checkIx "5" i (5 :: Int) (adtDeclStrs !! i)
  subtrees (LcAFun t1 t2) = Set.unions [subtrees t1, subtrees t2]
  subtrees n = Set.singleton n

instance HasStats LcAExpr where
  sizeFn (LcAInt _) = 1
  sizeFn (LcAPlus e1 e2) = 1 + sizeFn e1 + sizeFn e2
  sizeFn (LcALam _ e) = 1 + sizeFn e
  sizeFn (LcAVar _) = 1
  sizeFn (LcAApp e1 e2) = 1 + sizeFn e1 + sizeFn e2
  sizeFn (LcAConstr _ xs) = 1 + sum (map sizeFn xs)
  sizeFn (LcACase x xs) = 1 + sizeFn x + sum (map sizeFn xs)
  nodeFreqs (LcAInt i) = unit (Class "structure") ("Lit_" ++ show i)
  nodeFreqs (LcAPlus x y) =
    mergeFreqs
      [unit (Class "structure") "Plus", nodeFreqs x, nodeFreqs y]
  nodeFreqs (LcALam t x) =
    mergeFreqs
      [unit (Class "structure") "Lam", nodeFreqs t, nodeFreqs x]
  nodeFreqs (LcAVar i) = unit (Class "structure") ("Var_" ++ show i)
  nodeFreqs (LcAApp x y) =
    mergeFreqs
      [unit (Class "structure") "App", nodeFreqs x, nodeFreqs y]
  nodeFreqs (LcAConstr _ xs) =
    mergeFreqs
      ([unit (Class "structure") "Constr"] ++ map nodeFreqs xs)
  nodeFreqs (LcACase x xs) =
    mergeFreqs
      ([unit (Class "structure") "Case", nodeFreqs x] ++ map nodeFreqs xs)
  ungenerate (LcAInt i) = checkIx "6" i 10 [['0' .. '9'] !! i]
  ungenerate (LcAPlus x y) = 'p' : ungenerate x ++ ungenerate y
  ungenerate (LcALam t x) =
    'l' : ungenerate t ++ ungenerate x
  ungenerate (LcAVar i) = checkIx "7" i 3 (varStrs !! i)
  ungenerate (LcAApp x y) = 'a' : ungenerate x ++ ungenerate y
  ungenerate (LcAConstr i xs) = 'c' : show i ++ (concat (map ungenerate xs))
  ungenerate (LcACase x xs) = 'd' : ungenerate x ++ (concat (map ungenerate xs))

  subtrees n@(LcAInt _) = Set.singleton n
  subtrees n@(LcAPlus x y) = Set.unions [Set.singleton n, subtrees x, subtrees y]
  subtrees n@(LcALam _ x) = Set.insert n (subtrees x)
  subtrees n@(LcAVar _) = Set.singleton n
  subtrees n@(LcAApp x y) = Set.unions [Set.singleton n, subtrees x, subtrees y]
  subtrees n@(LcAConstr _ xs) = Set.unions (Set.singleton n : map subtrees xs)
  subtrees n@(LcACase x xs) = Set.unions (Set.singleton n : subtrees x : map subtrees xs)
