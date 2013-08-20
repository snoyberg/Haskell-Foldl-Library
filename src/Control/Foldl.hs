{-| This module provides efficient and streaming left folds that you can combine
    using 'Applicative' style.

    Import this module qualified to avoid clashing with the Prelude:

>>> import qualified Control.Foldl as L

    Use 'fold' to apply a 'Fold' to a list:

>>> L.fold L.sum [1..100]
5050

    'Fold's are 'Applicative's, so you can combine them using 'Applicative'
    combinators:

>>> import Control.Applicative
>>> let average = (/) <$> L.sum <*> L.genericLength

    These combined folds will still traverse the list only once, streaming
    efficiently over the list in constant space without space leaks:

>>> L.fold average [1..10000000]
5000000.5
>>> L.fold ((,) <$> L.minimum <*> L.maximum) [1..10000000]
(Just 1,Just 10000000)

    You can also unpack the `Fold` type if you want to extract the individual
    components of combined folds for use with your own customized folding
    utilities:

> case ((/) <$> L.sum <*> L.genericLength) of
>     L.Foldl step begin done -> ...
-}

{-# LANGUAGE ExistentialQuantification #-}

module Control.Foldl
    ( -- * Fold Types
      Fold(..)
    , fold
    , foldM
    , Step (..)

      -- * Folds
    , mconcat
    , foldMap
    , head
    , last
    , null
    , length
    , and
    , or
    , all
    , any
    , sum
    , product
    , maximum
    , minimum
    , elem
    , notElem
    , find
    , index
    , elemIndex
    , findIndex

      -- * Generic Folds
    , genericLength
    , genericIndex
    ) where

import Control.Applicative (Applicative(pure, (<*>)), (<$>))
import Data.Monoid (Monoid(mempty, mappend))
import Prelude hiding
    ( head
    , last
    , null
    , length
    , and
    , or
    , all
    , any
    , sum
    , product
    , maximum
    , minimum
    , elem
    , notElem
    , foldr
    )
import Data.Foldable (Foldable (foldr), toList)
import Control.Monad (liftM, ap)
import Data.Functor.Identity (Identity (..))

data Step m x = Continue !x
              | Stop !x
              | ContinueM !(m x)
              | StopM !(m x)

instance Monad m => Functor (Step m) where
    fmap f (Continue x) = Continue (f x)
    fmap f (Stop x) = Stop (f x)
    fmap f (ContinueM mx) = ContinueM (liftM f mx)
    fmap f (StopM mx) = StopM (liftM f mx)

instance Monad m => Applicative (Step m) where
    pure = Continue
    Stop x <*> Stop y = Stop (x y)
    Continue x <*> Continue y = Continue (x y)
    Stop x <*> Continue y = Continue (x y)
    Continue x <*> Stop y = Continue (x y)
    StopM mx <*> Stop y = StopM (mx `ap` return y)
    Stop x <*> StopM my = StopM (return x `ap` my)
    StopM mx <*> StopM my = StopM (mx `ap` my)
    Continue x <*> ContinueM my = ContinueM (return x `ap` my)
    ContinueM mx <*> Continue y = ContinueM (mx `ap` return y)
    ContinueM mx <*> ContinueM my = ContinueM (mx `ap` my)
    ContinueM mx <*> StopM my = ContinueM (mx `ap` my)
    StopM mx <*> ContinueM my = ContinueM (mx `ap` my)
    ContinueM mx <*> Stop y = ContinueM (mx `ap` return y)
    Stop x <*> ContinueM my = ContinueM (return x `ap` my)
    StopM mx <*> Continue y = ContinueM (mx `ap` return y)
    Continue x <*> StopM my = ContinueM (return x `ap` my)

{-| Efficient representation of a left fold that preserves the fold's step
    function, initial accumulator, and extraction function

    This allows the 'Applicative' instance to assemble derived folds that
    traverse the container only once
-}
data Fold m a b = forall x . Fold (x -> a -> Step m x) (Step m x) (x -> m b)

-- | Apply a strict left 'Fold' to a list and extract the final result
fold :: Foldable t => Fold Identity a b -> t a -> b
fold f as = runIdentity (foldM f as)
{-# INLINE fold #-}

data Pair a b = Pair !a !b

instance (Monad m) => Functor (Fold m a) where
    fmap f (Fold step start done) = Fold step start done'
      where
        done' x = do
            b <- done x
            return $! f b
    {-# INLINABLE fmap #-}

instance (Monad m) => Applicative (Fold m a) where
    pure b = Fold (\() _ -> pure ()) (pure ()) (\() -> return b)
    {-# INLINABLE pure #-}
    (Fold stepL beginL doneL) <*> (Fold stepR beginR doneR) =
        let step (Pair xL xR) a = Pair <$> stepL xL a <*> stepR xR a
            begin = Pair <$> beginL <*> beginR
            done (Pair xL xR) = do
                f <- doneL xL
                x <- doneR xR
                return $! f x
        in  Fold step begin done
    {-# INLINABLE (<*>) #-}

-- | Like 'fold', but monadic
foldM :: (Monad m, Foldable t) => Fold m a b -> t a -> m b
foldM (Fold step begin done) as0 = do
    loop (toList as0) begin
  where
    loop as (Continue x) = loop' as x

    loop'  []    x = done x
    loop' (a:as) x = loop as (step x a)
{-# INLINABLE foldM #-}

pureFold :: Monad m
         => (x -> a -> x)
         -> x
         -> (x -> b)
         -> Fold m a b
pureFold step begin done = Fold (\x y -> pure (step x y)) (pure begin) (return . done)

-- | Fold all values within a container using 'mappend' and 'mempty'
mconcat :: (Monoid a, Monad m) => Fold m a a
mconcat = pureFold mappend mempty id
{-# INLINABLE mconcat #-}

-- | Convert a \"@foldMap@\" to a 'Fold'
foldMap :: (Monoid w, Monad m) => (a -> w) -> (w -> b) -> Fold m a b
foldMap to from = pureFold (\x a -> mappend x (to a)) mempty from
{-# INLINABLE foldMap #-}

data Maybe' a = Just' !a | Nothing'

lazy :: Maybe' a -> Maybe a
lazy  Nothing'  = Nothing
lazy (Just' a') = Just a'

{-| Get the first element of a container or return 'Nothing' if the container is
    empty
-}
head :: Monad m => Fold m a (Maybe a)
head = pureFold step Nothing' lazy
  where
    step x a = case x of
        Nothing' -> Just' a
        _        -> x
{-# INLINABLE head #-}

{-| Get the last element of a container or return 'Nothing' if the container is
    empty
-}
last :: Monad m => Fold m a (Maybe a)
last = pureFold (\_ -> Just') Nothing' lazy
{-# INLINABLE last #-}

-- | Returns 'True' if the container is empty, 'False' otherwise
null :: Monad m => Fold m a Bool
null = Fold (\_ _ -> Stop False) (Continue True) return
{-# INLINABLE null #-}

-- | Return the length of the container
length :: Monad m => Fold m a Int
length = genericLength
{- Technically, 'length' is just 'genericLength' specialized to 'Int's.  I keep
   the two separate so that I can later provide an 'Int'-specialized
   implementation of 'length' for performance reasons like "GHC.List" does
   without breaking backwards compatibility.
-}
{-# INLINABLE length #-}

-- | Returns 'True' if all elements are 'True', 'False' otherwise
and :: Monad m => Fold m Bool Bool
and =
    Fold step (Continue True) return
  where
    step x y
        | x && y = Continue True
        | otherwise = Stop False
{-# INLINABLE and #-}

-- | Returns 'True' if any element is 'True', 'False' otherwise
or :: Monad m => Fold m Bool Bool
or =
    Fold step (Continue False) return
  where
    step x y
        | x || y = Stop True
        | otherwise = Continue False
{-# INLINABLE or #-}

mapInput :: Monad m => (a -> b) -> Fold m b c -> Fold m a c
mapInput f (Fold step begin done) =
    Fold step' begin done
  where
    step' x y = step x (f y)

{-| @(all predicate)@ returns 'True' if all elements satisfy the predicate,
    'False' otherwise
-}
all :: Monad m => (a -> Bool) -> Fold m a Bool
all predicate = mapInput predicate and
{-# INLINABLE all #-}

{-| @(any predicate)@ returns 'True' is any element satisfies the predicate,
    'False' otherwise
-}
any :: Monad m => (a -> Bool) -> Fold m a Bool
any predicate = mapInput predicate or
{-# INLINABLE any #-}

-- | Computes the sum of all elements
sum :: Monad m => (Num a) => Fold m a a
sum = pureFold (+) 0 id
{-# INLINABLE sum #-}

-- | Computes the product all elements
product :: (Num a, Monad m) => Fold m a a
product = pureFold (*) 1 id
{-# INLINABLE product #-}

-- | Computes the maximum element
maximum :: (Ord a, Monad m) => Fold m a (Maybe a)
maximum = pureFold step Nothing' lazy
  where
    step x a = Just' (case x of
        Nothing' -> a
        Just' a' -> max a a')
{-# INLINABLE maximum #-}

-- | Computes the minimum element
minimum :: (Ord a, Monad m) => Fold m a (Maybe a)
minimum = pureFold step Nothing' lazy
  where
    step x a = Just' (case x of
        Nothing' -> a
        Just' a' -> min a a')
{-# INLINABLE minimum #-}

{-| @(elem a)@ returns 'True' if the container has an element equal to @a@,
    'False' otherwise
-}
elem :: (Eq a, Monad m) => a -> Fold m a Bool
elem a = any (a ==)
{-# INLINABLE elem #-}

{-| @(notElem a)@ returns 'False' if the container has an element equal to @a@,
    'True' otherwise
-}
notElem :: (Eq a, Monad m) => a -> Fold m a Bool
notElem a = all (a /=)
{-# INLINABLE notElem #-}

{-| @(find predicate)@ returns the first element that satisfies the predicate or
    'Nothing' if no element satisfies the predicate
-}
find :: Monad m => (a -> Bool) -> Fold m a (Maybe a)
find predicate = Fold step (pure Nothing') (return . lazy)
  where
    step x a = case x of
        Nothing' -> if (predicate a) then Stop (Just' a) else Continue Nothing'
        _        -> Stop x
{-# INLINABLE find #-}

data Either' a b = Left' !a | Right' !b

{-| @(index n)@ returns the @n@th element of the container, or 'Nothing' if the
    container has an insufficient number of elements
-}
index :: Monad m => Int -> Fold m a (Maybe a)
index = genericIndex
{-# INLINABLE index #-}

{-| @(elemIndex a)@ returns the index of the first element that equals @a@, or
    'Nothing' if no element matches
-}
elemIndex :: (Eq a, Monad m) => a -> Fold m a (Maybe Int)
elemIndex a = findIndex (a ==)
{-# INLINABLE elemIndex #-}

{-| @(findIndex predicate)@ returns the index of the first element that
    satisfies the predicate, or 'Nothing' if no element satisfies the predicate
-}
findIndex :: Monad m => (a -> Bool) -> Fold m a (Maybe Int)
findIndex predicate = pureFold step (Pair 0 False) done
  where
    step x@(Pair i b) a =
        if b                  then x
        else if (predicate a) then Pair  i      True
        else                       Pair (i + 1) False
    done (Pair i b) = if b then Just i else Nothing
{-# INLINABLE findIndex #-}

-- | Like 'length', except with a more general 'Num' return value
genericLength :: (Num b, Monad m) => Fold m a b
genericLength = pureFold (\n _ -> n + 1) 0 id
{-# INLINABLE genericLength #-}

-- | Like 'index', except with a more general 'Integral' argument
genericIndex :: (Integral i, Monad m) => i -> Fold m a (Maybe a)
genericIndex i = pureFold step (Left' 0) done
  where
    step x a = case x of
        Left'  j -> if (i == j) then Right' a else Left' (j + 1)
        _        -> x
    done x = case x of
        Left'  _ -> Nothing
        Right' a -> Just a
{-# INLINABLE genericIndex #-}
