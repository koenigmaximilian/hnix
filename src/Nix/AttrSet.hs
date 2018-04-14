{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Nix.AttrSet where

import           Codec.Serialise (Serialise)
import qualified Codec.Serialise as Ser
import           Control.Arrow (first)
import           Control.DeepSeq
import           Control.Monad
import           Control.Monad.Free
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Except
import           Data.Align
import           Data.Align.Key
import           Data.Binary (Binary)
import qualified Data.Binary as Bin
import           Data.Binary.Orphans ()
import           Data.Data
import           Data.Either
import           Data.Eq.Deriving
import           Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as M
import           Data.List (sortOn)
import           Data.Maybe (fromMaybe, maybe, listToMaybe)
import           Data.Semigroup
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.These
import           GHC.Generics
import           Nix.Utils
import           Text.Megaparsec.Pos
import           Text.Show.Deriving

data AttrSetF r = AttrSetF
    { valMap :: HashMap Text r
    , posMap :: HashMap Text SourcePos
    }
    deriving (Show, Eq, Ord, Generic, Generic1, Typeable, Data,
              Functor, Foldable, Traversable, NFData, Serialise)

instance Semigroup (AttrSetF a) where
    AttrSetF valx posx <> AttrSetF valy posy =
        AttrSetF (valx `M.union` valy) (posx `M.union` posy)

instance Monoid (AttrSetF a) where
    mempty = AttrSetF M.empty M.empty
    mappend = (<>)

instance Serialise Pos where
    encode x = Ser.encode (unPos x)
    decode = mkPos <$> Ser.decode

instance Serialise SourcePos where
    encode (SourcePos f l c) = Ser.encode f <> Ser.encode l <> Ser.encode c
    decode = SourcePos <$> Ser.decode <*> Ser.decode <*> Ser.decode

instance Binary Pos where
    put x = Bin.put (unPos x)
    get = mkPos <$> Bin.get
instance Binary SourcePos
instance Binary a => Binary (AttrSetF a)

$(deriveEq1 ''AttrSetF)
$(deriveShow1 ''AttrSetF)

{-
instance (NFData (f (Free f a)), NFData a) => NFData (Free f a) where
    rnf (Pure x) = rnf x
    rnf (Free f) = rnf f

instance (Serialise (f (Free f a)), Serialise a)
      => Serialise (Free f a) where
    encode (Pure x) = Ser.encode False <> Ser.encode x
    encode (Free f) = Ser.encode True <> Ser.encode f
    decode = Ser.decode >>= \case
        False -> Pure <$> Ser.decode
        True -> Free <$> Ser.decode

newtype AttrSet a = AttrSet (Free AttrSetF a)
    deriving (Eq, Generic, Generic1, Typeable, Data,
              Functor, Foldable, Traversable, Applicative, Monad,
              NFData, Serialise)

$(deriveEq1 ''AttrSet)
-}

type AttrSet = Free AttrSetF

instance Semigroup (AttrSet a) where
    Free (AttrSetF valx posx) <> Free (AttrSetF valy posy) =
        Free $ AttrSetF (valx `M.union` valy) (posx `M.union` posy)
    _ <> _ = error "Use of <> on non-Free attr sets has no meaning"

instance Monoid (AttrSet a) where
    mempty = emptyAttrSet
    mappend = (<>)

showAttrSet :: Show a => AttrSet a -> String
showAttrSet m =
    "{ " ++ concat [ renderPath k ++ " = " ++ show v ++ "; "
                   | (k, v) <- sortOn fst $ attrsetToList m ] ++ "}"

class AttrSetProjects m a | a -> m where
    -- | Attempt to project a value stored in an attribute to an attribute set
    --   itself. This should raise an error in 'm' if not possible, so it is
    --   assumed to always succeed.
    projectAttrSet :: a -> m (AttrSet a)
    projectAttrSetMay :: a -> m (Maybe (AttrSet a))

class AttrSetEmbeds a where
    embedAttrSet :: AttrSet a -> a

emptyAttrSet :: AttrSet a
emptyAttrSet = Free (AttrSetF M.empty M.empty)

singletonAttrSet :: Text -> Maybe SourcePos -> a -> AttrSet a
singletonAttrSet k p v =
    Free (AttrSetF (M.singleton k (Pure v))
                   (maybe M.empty (M.singleton k) p))

keyInsert :: (Monad m, AttrSetProjects m a)
          => Text -> Maybe SourcePos -> a -> AttrSet a
          -> m (AttrSet a)
keyInsert k mpos v (Pure a) = keyInsert k mpos v =<< projectAttrSet a
keyInsert k mpos v (Free (AttrSetF mv mp)) =
    return $ Free (AttrSetF (M.insert k (Pure v) mv)
                            (maybe mp (M.insert k ?? mp) mpos))

pathInsert :: (Monad m, AttrSetProjects m a)
       => [Text] -> [Maybe SourcePos] -> a -> AttrSet a
       -> m (AttrSet a)
pathInsert [] _ _ m              = return m
pathInsert [k] pos v attrs       = keyInsert k (join (listToMaybe pos)) v attrs
pathInsert (k:ks) pos v (Pure m) = pathInsert (k:ks) pos v =<< projectAttrSet m
pathInsert (k:ks) pos v (Free (AttrSetF mv mp)) = do
    t <- pathInsert ks (tailIf pos) v
                   (fromMaybe (Free mempty) (M.lookup k mv))
    return $ Free $ AttrSetF
        (M.insert k t mv)
        (maybe mp (M.insert k ?? mp) (join (listToMaybe pos)))
  where
    tailIf [] = []
    tailIf (_:ps) = ps

keyLookup :: Text -> AttrSet a -> Maybe (Either (AttrSet a) a)
keyLookup _ (Pure _) =
    error "Attempt to look up key in value not known to be a set"
keyLookup k (Free (AttrSetF m _)) = case M.lookup k m of
    Nothing       -> Nothing
    -- Hide the use of 'free' from the caller
    Just (Pure a) -> Just (Right a)
    Just a        -> Just (Left a)

pathLookup :: (Monad m, AttrSetProjects m a)
           => [Text] -> AttrSet a -> m (Maybe (Either (AttrSet a) a))
pathLookup [] _            = return Nothing
pathLookup (k:ks) (Pure a) = projectAttrSetMay a >>= \case
    Nothing -> return Nothing
    Just m  -> pathLookup (k:ks) m
pathLookup [k] attrs       = return $ keyLookup k attrs
pathLookup (k:ks) (Free (AttrSetF mv _)) = case M.lookup k mv of
    Nothing -> return Nothing
    Just m  -> pathLookup ks m

lookupPos :: (Monad m, AttrSetProjects m a)
          => Text -> AttrSet a -> m (Maybe SourcePos)
lookupPos k (Pure a) = projectAttrSetMay a >>= \case
    Nothing -> return Nothing
    Just m  -> lookupPos k m
lookupPos k (Free (AttrSetF _ m)) = return $ M.lookup k m

attrsetFromList :: (Monad m, AttrSetProjects m a)
                => [([(Text, Maybe SourcePos)], a)] -> m (AttrSet a)
attrsetFromList [] = return $ Free mempty
attrsetFromList ((unzip -> (ks, ps), v):xs) =
    pathInsert ks ps v =<< attrsetFromList xs

attrsetToList :: AttrSet a -> [([(Text, Maybe SourcePos)], a)]
attrsetToList (Pure a) = [([], a)]
attrsetToList (Free (AttrSetF mv mp)) =
    let m = concat
          $ M.elems
          $ (\f -> alignWithKey f mv mp)
          $ \k -> \case These x p -> go (k, Just p) x
                        This x    -> go (k, Nothing) x
                        _ -> []
    in m
  where
    go k (Pure a) = [([k], a)]
    go k m = map (first (k:)) (attrsetToList m)

attrsetCompare :: (Monad m, AttrSetProjects m a, AttrSetProjects m b)
               => (a -> b -> m Bool) -> AttrSet a -> AttrSet b -> m Bool
attrsetCompare eq (Pure x) (Pure y) = x `eq` y
attrsetCompare eq (Pure x) y = projectAttrSetMay x >>= \case
    Nothing -> return False
    Just m  -> attrsetCompare eq m y
attrsetCompare eq x (Pure y) = projectAttrSetMay y >>= \case
    Nothing -> return False
    Just m  -> attrsetCompare eq x m
attrsetCompare eq (Free (AttrSetF xm _)) (Free (AttrSetF ym _)) =
    fmap isRight $ runExceptT $ do
        pairs <- forM (align xm ym) $ \case
            These a b -> return (a, b)
            _ -> throwE ()
        forM_ pairs $ \(a, b) -> guard =<< lift (attrsetCompare eq a b)

renderPath :: [(Text, Maybe SourcePos)] -> String
renderPath = Text.unpack . Text.intercalate "." . map fst
