{-# LANGUAGE PolyKinds, 
             DataKinds, 
             TypeFamilies, 
             KindSignatures, 
             GADTs,
             FlexibleInstances, 
             MultiParamTypeClasses,
             ScopedTypeVariables #-}

-- Tested with GHC version 7.4.1

module RedBlack where

-- Red Black Trees that use GADTs to statically enforce the redblack
-- tree invariants. This version of the file statically enforces all
-- the following invariants of Red Black Trees are preserved by the 
-- insertion function.

-- 1. Leaf nodes are Black
-- 2. Red nodes have Black children
-- 3. Root is Black
-- 4. Black height is same for all paths from root to leaves

-- Author: Stephanie Weirich

import Control.Monad 
import Test.QuickCheck hiding (elements)
import Data.Maybe as Maybe

data Color = R | B deriving (Eq, Show)

-- The Sing family, kind polymorphic
data family Sing a :: *
     
-- singleton type for colors     
data instance Sing (c :: Color) where 
  SR :: Sing R 
  SB :: Sing B 

instance Show (Sing (c :: Color)) where
  show SR = "SR"
  show SB = "SB"

data Nat = S Nat | Z   
  
-- Force red nodes have black children. 
-- Uses a multiparameter type class to describe the allowable *relation*
-- between the color of the children (c1 & c2) and the color of 
-- the node (c3).

class Valid (c1 :: Color) (c2 :: Color) (c3 :: Color) 
instance Valid B B R 
instance Valid x y B
         
 -- a type function to "conditionally increment" the black height
type family Inc (c :: Color) (n :: Nat) :: Nat
type instance Inc B n = S n   -- if the node is black, increment
type instance Inc R n = n     -- if red, preserve the height

-- GADT for Red black trees, where the type indices indicate
-- the color of the node at the top of the tree and the black
-- height.
data T (c :: Color) (n :: Nat) (a :: *) where 
  E :: T B Z a
  N :: Valid c1 c2 c3 => Sing c3 ->
       T c1 n a -> a -> T c2 n a -> T c3 (Inc c3 n) a
       
instance Show a => Show (T c n a) where       
  show E = "E"
  show (N c a x b) = "(N " ++ show c ++ " " ++ show a ++ " " ++ show x 
                     ++ " " ++ show b ++ ")"

-- Top-level type for Red/Black trees
-- Enforces that the root is black and hides the black height 
data RBT a where
     Root :: (T B n a) -> RBT a
     
instance (Show a) => (Show (RBT a)) where
    show (Root t) = show t
     

color :: T c n a -> Sing c
color E = SB
color (N c _ _ _) = c

empty :: RBT a
empty = Root E

member :: Ord a => a -> RBT a -> Bool
member x (Root t) = aux x t where
  aux :: Ord a => a -> T c n a -> Bool
  aux x E = False
  aux x (N _ a y b) | x < y     = aux x a
                    | x > y     = aux x b
                    | otherwise = True

elements :: Ord a => RBT a -> [a]
elements (Root t) = aux t [] where
  aux :: Ord a => T c n a -> [a] -> [a]
  aux E xs = xs
  aux (N _ a y b) xs = aux a (y : aux b xs)   

-- A node where the second invariant is allowed to be "slightly" broken
-- This node can be red even though one or both of its children are red. 
-- However, it must preserve the black height invariant.
  
data Node n a where
     Node :: (Sing c) -> (T c1 n a) -> a -> (T c2 n a) -> Node (Inc c n) a

-- When we call ins, we don't know what color it will produce, and
-- invariant 2 may be broken in the result. But we do know that the
-- black height will be the same as it was before.
     
ins :: Ord a => a -> T c n a -> Node n a
ins x E = Node SR E x E
ins x s@(N c a y b) 
  | x < y  = balanceL c (ins x a) y b
  | x > y  = balanceR c a y (ins x b)
  | otherwise = (Node c a y b)

-- Rebalance after an insertion on the left. This function is allowed
-- to return a tree that violates invariant 2 at the root, but the
-- rest of of the tree must be valid.  
balanceL :: Ord a => 
  Sing c -> Node n a -> a -> T c1 n a -> Node (Inc c n) a
balanceL SB (Node SR (N SR a x b) y c) z d =   -- rotation required
    (Node SR (N SB a x b) y (N SB c z d)) 
balanceL SB (Node SR a x (N SR b y c)) z d =   -- rotation required
    (Node SR (N SB a x b) y (N SB c z d))
    
-- The rest of these cases just put the tree back together 
-- without rearranging any of the elements. We would like to 
-- just write:
--     balanceL c (Node c' a x b) y d = Node c (N c' a x b) y d
-- but we don't know that "N c' a x b" is a valid red/black tree.
-- Instead, we have do some extra pattern matching to explicitly 
-- identify the good cases. The compiler doesn't check that the pattern
-- match is exhaustive

-- If the top of the new left subtree is black, then we know 
-- that *it* satisfies property 2 trivially. Even if c is red 
-- and the color of b is red, we don't need to rebalance because 
-- that is an allowable deviation from property 2.
balanceL c (Node SB a' x' b') x b = (Node c (N SB a' x' b') x b)    
    
-- on the other hand, if the top of the new left subtree is red,  
-- we need to show that *its* subtrees must be black. We know that 
-- is the case, because we checked all of the cases they could be 
-- red above. However, GHC checks these cases individually, so we 
-- have to go through them here.  There are two ways trees could be 
-- black, either they are internal 'T' nodes, marked SB, or leaf nodes
-- 'E', which are always black. 
balanceL c (Node SR a'@(N SB _ _ _) x' b'@(N SB _ _ _)) x b = 
    (Node c (N SR a' x' b') x b)    
balanceL c (Node SR a'@E x' b'@E) x b = 
    (Node c (N SR a' x' b') x b)    
-- -- we only care about the above two cases, because these two 
-- -- patterns violate the black height property. They don't type
-- -- check.
-- balanceL c (Node SR a'@E x' b'@(N SB _ _ _)) x b = 
--    (Node c (N SR a' x' b') x b)      
-- balanceL c (Node SR a'@(N SB _ _ _) x' b'@E) x b = 
--    (Node c (N SR a' x' b') x b)    

-- These two cases, however, typecheck but are impossible. We don't have 
-- enough static information to rule them out here, so we cannot show that
-- insert is a total function.
balanceL SR (Node SR (N SR a x b) y c) z d = 
  error "impossible"
balanceL SR (Node SR c y (N SR a x b)) z d = 
  error "impossible"
  
    
-- Need the symmetric cases for balanceR    
balanceR :: Ord a =>   
   Sing c -> T c1 n a -> a -> Node n a -> Node (Inc c n) a
balanceR SB a x (Node SR (N SR b y c) z d) = 
    (Node SR (N SB a x b) y (N SB c z d))
balanceR SB a x (Node SR b y (N SR c z d)) = 
    (Node SR (N SB a x b) y (N SB c z d))
balanceR c a x (Node SB a' x' b') =
    (Node c a x (N SB a' x' b'))
balanceR c a x (Node SR a'@(N SB _ _ _) x' b'@(N SB _ _ _)) =
    (Node c a x (N SR a' x' b'))
balanceR c a x (Node SR a'@E x' b'@E) =
    (Node c a x (N SR a' x' b'))
balanceR SR d z (Node SR (N SR a x b) y c) = 
  error "impossible"
balanceR SR d z (Node SR c y (N SR a x b)) = 
  error "impossible"

-- top-level insertion function
insert :: Ord a => a -> RBT a -> RBT a
insert x (Root t) = blacken (ins x t) where
   blacken (Node _ a x b) = (Root (N SB a x b))

-- using quickcheck to verify the tree.
instance (Ord a, Arbitrary a) => Arbitrary (RBT a)  where
   arbitrary = liftM (foldr insert empty) arbitrary

-- properties to ensure that insert is correct
prop_insert1 :: Int -> RBT Int -> Bool
prop_insert1 x t = member x (insert x t)

prop_insert2 :: Int -> RBT Int -> Bool
prop_insert2 x t = all (\y -> member y (insert x t)) (elements t) 

