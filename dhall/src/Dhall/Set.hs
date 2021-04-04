{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DeriveLift         #-}

-- | This module only exports ways of constructing a Set,
-- retrieving List, Set, and Seq representations of the same data,
-- as well as a novel "difference" function.
-- Any other Set-like or List-like functionality
-- should be obtained through toSet and toList, respectively.
module Dhall.Set (
      Set(..)
    , toList
    , toAscList
    , toSet
    , toSeq
    , fromList
    , fromSet
    , append
    , empty
    , difference
    , sort
    , isSorted
    , null
    , size
    ) where

import Control.DeepSeq            (NFData)
import Data.Data                  (Data)
import Data.List                  (foldl')
import Data.Sequence              (Seq, (|>))
import GHC.Generics               (Generic)
import Instances.TH.Lift          ()
import Language.Haskell.TH.Syntax (Lift)
import Prelude                    hiding (null)

import qualified Data.Foldable
import qualified Data.Sequence
import qualified Data.Set

{-| This is a variation on @"Data.Set".`Data.Set.Set`@ that remembers the
    original order of elements.  This ensures that ordering is not lost when
    formatting Dhall code
-}
data Set a = Set (Data.Set.Set a) (Seq a)
    deriving (Generic, Show, Data, NFData, Lift)
-- Invariant: In @Set set seq@, @toAscList set == sort (toList seq)@.

instance Eq a => Eq (Set a) where
    (Set _ x) == (Set _ y) = x == y
    {-# INLINABLE (==) #-}

instance Ord a => Ord (Set a) where
    compare (Set _ x) (Set _ y) = compare x y
    {-# INLINABLE compare #-}

instance Foldable Set where
    foldMap f (Set _ x) = foldMap f x
    {-# INLINABLE foldMap #-}

    toList = Dhall.Set.toList
    {-# INLINABLE toList #-}

    null = Dhall.Set.null
    {-# INLINABLE null #-}

    length = Dhall.Set.size
    {-# INLINABLE length #-}

-- | Convert to an unordered @"Data.Set".`Data.Set.Set`@
toSet :: Set a -> Data.Set.Set a
toSet (Set s _) = s

-- | Convert to an ordered `Seq`
toSeq :: Set a -> Seq a
toSeq (Set _ xs) = xs

-- | Convert a `Set` to a list, preserving the original order of the elements
toList :: Set a -> [a]
toList (Set _ xs) = Data.Foldable.toList xs

-- | Convert a `Set` to a list of ascending elements
toAscList :: Set a -> [a]
toAscList (Set s _) = Data.Set.toAscList s

-- | Convert a list to a `Set`, remembering the element order
fromList :: Ord a => [a] -> Set a
fromList = foldl' (flip append) empty
-- O(n log n) time complexity, O(n) space complexity.
-- Implementing it this way is a little silly, but is faster than (nub xs).
-- n.b. toList . fromList = id, only if the list elements are unique

-- | Convert a @"Data.Set".`Data.Set.Set`@ to a sorted `Set`
fromSet :: Data.Set.Set a -> Set a
fromSet s = Set s (Data.Sequence.fromList (Data.Set.elems s))

-- | Append an element to the end of a `Set`
append :: Ord a => a -> Set a -> Set a
append x os@(Set s xs)
    | Data.Set.member x s = os
    | otherwise = Set (Data.Set.insert x s) (xs |> x)
-- O(log n) time complexity.

-- | The empty `Set`
empty :: Set a
empty = Set Data.Set.empty Data.Sequence.empty

-- | Returns, in order, all elements of the first Set not present in the second.
-- (It doesn't matter in what order the elements appear in the second Set.)
difference :: Ord a => Set a -> Set a -> [a]
difference os (Set s _) =
    filter (\ x -> not (Data.Set.member x s)) (toList os)

{-| Sort the set elements, forgetting their original ordering.

>>> sort (fromList [2, 1]) == fromList [1, 2]
True
-}
sort :: Ord a => Set a -> Set a
sort (Set s _) = Set s (Data.Sequence.fromList (Data.Set.toList s))

{-|
>>> isSorted (fromList [2, 1])
False
>>> isSorted (fromList [1, 2])
True
-}
isSorted :: Ord a => Set a -> Bool
isSorted s = toList s == Data.Set.toList (toSet s)

{-|
>>> null (fromList [1])
False
>>> null (fromList [])
True
-}
null :: Set a -> Bool
null (Set s _) = Data.Set.null s

{-|
>>> size (fromList [1])
1
-}
size :: Set a -> Int
size (Set s _) = Data.Set.size s
