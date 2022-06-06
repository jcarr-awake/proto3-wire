{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}


module Main where

import qualified Data.ByteString               as B
import qualified Data.ByteString.Lazy          as BL
import qualified Proto3.Wire.Decode as De
import qualified Proto3.Wire.Encode as En
import Proto3.Wire

import Control.Applicative (liftA3)
import Data.Maybe
import Data.Word
import Data.IORef

import Criterion (bgroup, bench)
import qualified Criterion as C
import Criterion.Main (defaultMain)

import Control.DeepSeq
import Data.Functor.Identity
import Data.Functor.Compose
import GHC.Exts ( reallyUnsafePtrEquality# )
import Text.Show.Pretty
import System.Random

import Debug.Trace


data Solo a = Solo a
  deriving (Functor)
instance Applicative Solo where
  pure = Solo
  Solo f <*> Solo x = Solo (f x)

data Tree f a = Leaf | Branch a (f (Tree f a)) (f (Tree f a))
  deriving (Functor)

instance (Traversable f, NFData a) => NFData (Tree f a) where
  rnf Leaf = ()
  rnf (Branch x t1 t2) =
    let rnf' x = case rnf x of () -> Solo x
    in case (rnf x, traverse rnf' t1, traverse rnf' t2) of
      ((), Solo _, Solo _) -> ()

instance (Functor f, Foldable f) => Foldable (Tree f) where
  foldMap f Leaf = mempty
  foldMap f (Branch x t1 t2) =
    (foldMap.foldMap) f t1 <> f x <> (foldMap.foldMap) f t2


  sum Leaf = 0
  sum (Branch a t1 t2) =
    let !a1 = sum . fmap sum $ t1
        !a2 = sum . fmap sum $ t2
    in a + a1 + a2

instance (Eq (f (Tree f a)), Eq a) => Eq (Tree f a) where
  Leaf == Leaf = True
  (Branch x1 t11 t12) == (Branch x2 t21 t22) = x1 == x2 && t11 == t21 && t12 == t22
  _ == _ = False

instance (Show (f (Tree f a)), Show a) => Show (Tree f a) where
  showsPrec _ Leaf = ('*':)
  showsPrec _ (Branch x t1 t2) =
    ('(' :) . shows t1 . ("<-(" ++) . shows x . ("->(" ++) .  shows t2 . (')' :)

treeHomM :: (Monad m, Traversable f) => (forall x. f x -> m (g x)) -> Tree f a -> m (Tree g a)
treeHomM f Leaf = pure Leaf
treeHomM f (Branch x l r) = Branch x <$> (traverse (treeHomM f) l >>= f) <*> (traverse (treeHomM f) r >>= f)

type UnparsedTreeRec f a = Either De.ParseError (B.ByteString, Tree f a) -> Either De.ParseError (f (Tree f a))

type Delayed = Compose (Either De.ParseError) ((,) B.ByteString)



intTreeDelayedParser :: Applicative f => UnparsedTreeRec f Word64 -> De.Parser De.RawMessage (Tree f Word64)
intTreeDelayedParser f = liftA3 combine
    (De.at (De.repeated De.fixed64) (FieldNumber 0))
    (De.unwrapParser $ De.at (De.one (f <$> De.embeddedDelayed' (intTreeDelayedParser f)) (pure $ pure Leaf)) (FieldNumber 1))
    (De.unwrapParser $ De.at (De.one (f <$> De.embeddedDelayed' (intTreeDelayedParser f)) (pure $ pure Leaf)) (FieldNumber 2))
  where
    combine xs y z = Branch (sum xs) y z


intTreeParser :: De.Parser De.RawMessage (Tree Identity Word64)
intTreeParser = liftA3 combine
    (De.at (De.repeated De.fixed64) (FieldNumber 0))
    (Identity <$> De.at (De.one (De.embedded' intTreeParser) Leaf) (FieldNumber 1))
    (Identity <$> De.at (De.one (De.embedded' intTreeParser) Leaf) (FieldNumber 2))
  where
    combine xs y z = Branch (sum xs) y z


intTreeEncoder :: Foldable f => Tree f Word64 -> En.MessageBuilder
intTreeEncoder Leaf = mempty
intTreeEncoder (Branch w t1 t2) = mconcat [ En.fixed64 (FieldNumber 0) w
                                          , En.embedded (FieldNumber 1) $ foldMap intTreeEncoder t1
                                          , En.embedded (FieldNumber 2) $ foldMap intTreeEncoder t2
                                          ]
{-# SPECIALIZE intTreeEncoder :: Tree Identity Word64 -> En.MessageBuilder #-}
{-# SPECIALIZE intTreeEncoder :: Tree Delayed Word64 -> En.MessageBuilder #-}

smartIntTreeEncoder :: Delayed (Tree Delayed Word64) -> Delayed (Tree Delayed Word64) -> En.MessageBuilder
smartIntTreeEncoder (Compose (Right (bs, t))) (Compose (Right (_, t'))) | 1# <- reallyUnsafePtrEquality# t t' =
  En.unsafeFromLazyByteString $ BL.fromStrict bs
smartIntTreeEncoder (Compose (Right (bs, t))) (Compose (Right (_, t'))) =
    case t' of
    Leaf -> mempty
    (Branch w' t1' t2') -> case t of
      Branch w t1 t2 ->
        mconcat
          [ En.fixed64 (FieldNumber 0) w'
          , En.embedded (FieldNumber 1) $ smartIntTreeEncoder t1 t1'
          , En.embedded (FieldNumber 2) $ smartIntTreeEncoder t1 t2'
          ]
      Leaf ->
        mconcat
          [ En.fixed64 (FieldNumber 0) w'
          , En.embedded (FieldNumber 1) $ foldMap intTreeEncoder t1'
          , En.embedded (FieldNumber 2) $ foldMap intTreeEncoder t2'
          ]
smartIntTreeEncoder _ _ = mempty


detRandom :: [Word64]
detRandom = concat . replicate 10 $
  [ 227, 133, 16, 164, 43,
    159, 207, 87, 180, 236,
    245, 128, 249, 170, 216,
    181, 164, 162, 239, 249,
    76, 237, 197, 246, 209,
    231, 124, 154, 55, 64,
    4, 114, 79, 199, 252,
    163, 116, 237, 209, 138,
    240, 148, 212, 224, 88,
    131, 122, 114, 158, 97,
    186, 3, 223, 230, 223,
    207, 93, 168, 48, 130,
    77, 122, 30, 222, 221,
    224, 243, 19, 175, 61,
    112, 246, 201, 57, 185,
    19, 128, 129, 138, 209,
    4, 153, 196, 238, 72,
    254, 157, 233, 81, 30,
    106, 249, 57, 214, 104,
    171, 146, 175, 185, 192,
    159, 207, 87, 180, 236,
    227, 133, 16, 164, 43,
    245, 128, 249, 170, 216,
    181, 164, 162, 239, 249,
    76, 237, 197, 246, 209,
    231, 124, 154, 55, 64,
    4, 114, 79, 199, 252,
    163, 116, 237, 209, 138,
    240, 148, 212, 224, 88,
    131, 122, 114, 158, 97,
    186, 3, 223, 230, 223,
    207, 93, 168, 48, 130,
    77, 122, 30, 222, 221,
    224, 243, 19, 175, 61,
    112, 246, 201, 57, 185,
    19, 128, 129, 138, 209,
    4, 153, 196, 238, 72,
    254, 157, 233, 81, 30,
    106, 249, 57, 214, 104,
    171, 146, 175, 185, 192,
    159, 207, 87, 180, 236,
    227, 133, 16, 164, 43,
    245, 128, 249, 170, 216,
    181, 164, 162, 239, 249,
    76, 237, 197, 246, 209,
    231, 124, 154, 55, 64,
    4, 114, 79, 199, 252,
    163, 116, 237, 209, 138,
    240, 148, 212, 224, 88,
    131, 122, 114, 158, 97,
    186, 3, 223, 230, 223,
    207, 93, 168, 48, 130,
    77, 122, 30, 222, 221,
    224, 243, 19, 175, 61,
    112, 246, 201, 57, 185,
    19, 128, 129, 138, 209,
    4, 153, 196, 238, 72,
    254, 157, 233, 81, 30,
    106, 249, 57, 214, 104,
    171, 146, 175, 185, 192
    ]

pullInt :: IORef [Word64] -> IO Word64
pullInt xs = do
  xs' <- readIORef xs
  case xs' of
    [] -> pure 7
    x : xs' -> do
      writeIORef xs xs'
      pure x

genInt :: IORef Int -> IO Word64
genInt count = do
  count' <- readIORef count
  if count' <= 0 then pure 7 else do
    writeIORef count (count' - 1)
    randomIO

mkTree0 :: IO Word64 -> IO En.MessageBuilder
mkTree0 ints = do
  shouldFork <- (\(i :: Word64) -> (i `mod` 8) < 7) <$> ints
  if shouldFork
    then do
      i <- En.fixed64 (FieldNumber 0) <$> ints
      left <- En.embedded (FieldNumber 1) <$> mkTree0 ints
      right <- En.embedded (FieldNumber 2) <$> mkTree0 ints
      pure (i <> left <> right)
    else pure mempty

mkTree :: IO B.ByteString
mkTree = BL.toStrict . En.toLazyByteString <$> (newIORef detRandom >>= mkTree0 . pullInt)

mkRandomTree :: IO B.ByteString
mkRandomTree = BL.toStrict . En.toLazyByteString <$> (newIORef 5000 >>= mkTree0 . genInt)

mkParsed :: Applicative f => UnparsedTreeRec f Word64 -> IO (Tree f Word64)
mkParsed f = do
  inp <- mkRandomTree
  Right t <- pure (De.parse (intTreeDelayedParser f) inp)
  pure t

mkSmart = mkParsed (Right . Compose)
mkNaive = mkParsed (fmap (Identity . snd))

decodeW :: B.ByteString -> IO (Maybe Word64)
decodeW = pure . fmap sum . toMaybe . De.parse intTreeParser
  where
    toMaybe (Left _) = Nothing
    toMaybe (Right x) = Just x

modifyTree :: Functor f => Tree f Word64 -> Tree f Word64
modifyTree (Branch x b t3) = Branch x b' t3
  where b' = fmap switch b
        switch :: Functor f => Tree f Word64 -> Tree f Word64
        switch (Branch y t1 t2) | 0 <- y `mod` 5 = Branch (y + 1) (modifyTree <$> t1) (modifyTree <$> t2)
        switch (Branch y t1 t2) | 1 <- y `mod` 5 = Branch (y + 1) (modifyTree <$> t1) (modifyTree <$> t2)
        switch (Branch y t1 t2) | 2 <- y `mod` 5 = Branch (y + 1) (modifyTree <$> t1) (modifyTree <$> t2)
        switch (Branch y t1 t2) | 3 <- y `mod` 5 = Branch (y + 1) t1 (modifyTree <$> t2)
        switch t = t
modifyTree t = t

updateSmart :: Tree Delayed Word64 -> IO B.ByteString
updateNaive :: Traversable f => Tree f Word64 -> IO B.ByteString
updateSmart t =
  let t' = modifyTree t
      encoded = smartIntTreeEncoder (pure t) (pure t')
  in pure . BL.toStrict . En.toLazyByteString $ encoded

updateNaive t =
     let t' = modifyTree t in
     pure . BL.toStrict . En.toLazyByteString . intTreeEncoder $ t'

main :: IO ()
main = do
  let f :: Tree Delayed Word64 -> C.Benchmark
      f tree = bgroup "Modifies"
                [ bench "Modify smart" (C.nfIO $ updateSmart tree)
                , bench "Modify naive" (C.nfIO $ updateNaive tree)
                , C.env stripDelayed $ bench "baseline" . C.nfIO . updateNaive
                ]
        where
          toIdentity :: Delayed x -> Either De.ParseError (Identity x)
          toIdentity (Compose (Left err)) = Left err
          toIdentity (Compose (Right (_, x))) = Right (Identity x)

          stripDelayed :: IO (Tree Identity Word64)
          stripDelayed = do
            Right t <- pure $ treeHomM toIdentity tree
            pure t
  defaultMain
    [ bench "Parse int tree" $ C.perBatchEnv (const mkTree) decodeW
    , C.env mkSmart f
    ]
