{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Nix.Value where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Data.Align
import Data.Fix
import Data.Monoid (appEndo)
import Data.Text (Text, pack)
import Data.These
import Data.Typeable (Typeable)
import GHC.Generics
import Nix.Atoms
import Nix.AttrSet
import Nix.Expr.Types
import Nix.Expr.Types.Annotated (SourcePos(..), unPos)
import {-# SOURCE #-} Nix.Stack
import Nix.Thunk
import Nix.Utils

-- | An 'NValue' is the most reduced form of an 'NExpr' after evaluation
-- is completed.
data NValueF m r
    = NVConstant NAtom
     -- | A string has a value and a context, which can be used to record what a
     -- string has been build from
    | NVStr Text (DList Text)
    | NVPath FilePath
    | NVList [r]
    | NVSet (AttrSet r)
      -- ^ An requirement of attrsets kept in NVSet is that their head is
      --   always 'Free' and never 'Pure'. Errors will be raised in several
      --   places if the latter ever happen.
    | NVClosure (Params ()) (m (NValue m) -> m (NValue m))
      -- ^ A function is a closed set of parameters representing the "call
      --   signature", used at application time to check the type of arguments
      --   passed to the function. Since it supports default values which may
      --   depend on other values within the final argument set, this
      --   dependency is represented as a set of pending evaluations. The
      --   arguments are finally normalized into a set which is passed to the
      --   function.
      --
      --   Note that 'm r' is being used here because effectively a function
      --   and its set of default arguments is "never fully evaluated". This
      --   enforces in the type that it must be re-evaluated for each call.
    | NVBuiltin String (NThunk m -> m (NValue m))
      -- ^ A builtin function is itself already in normal form. Also, it may
      --   or may not choose to evaluate its argument in the production of a
      --   result.
    deriving (Generic, Typeable, Functor)

-- | An 'NValueNF' is a fully evaluated value in normal form. An 'NValue m' is
--   a value in head normal form, where only the "top layer" has been
--   evaluated. An action of type 'm (NValue m)' is a pending evualation that
--   has yet to be performed. An 'NThunk m' is either a pending evaluation, or
--   a value in head normal form. A 'NThunkSet' is a set of mappings from keys
--   to thunks.

type    NValueNF m = Fix (NValueF m)      -- normal form
newtype NThunk m   = NThunk (Thunk m (NValue m))
type    NValue m   = NValueF m (NThunk m) -- head normal form
type    ValueSet m = AttrSet (NThunk m)

instance Show (NValueF m (Fix (NValueF m))) where
    showsPrec = flip go where
      go (NVConstant atom)    = showsCon1 "NVConstant" atom
      go (NVStr text context) = showsCon2 "NVStr"      text (appEndo context [])
      go (NVList     list)    = showsCon1 "NVList"     list
      go (NVSet attrs)        = showsCon1 "NVSet"      attrs
      go (NVClosure p _)      = showsCon1 "NVClosure"  p
      go (NVPath p)           = showsCon1 "NVPath"     p
      go (NVBuiltin name _)   = showsCon1 "NVBuiltin"  name

      showsCon1 :: Show a => String -> a -> Int -> String -> String
      showsCon1 con a d =
          showParen (d > 10) $ showString (con ++ " ") . showsPrec 11 a

      showsCon2 :: (Show a, Show b)
                => String -> a -> b -> Int -> String -> String
      showsCon2 con a b d =
          showParen (d > 10)
              $ showString (con ++ " ")
              . showsPrec 11 a
              . showString " "
              . showsPrec 11 b

instance (Framed e m, MonadFile m, MonadVar m,
          MonadThunk (NValue m) (NThunk m) m, Show (NValue m))
      => AttrSetProjects m (NThunk m) where
    projectAttrSetMay t = force @(NValue m) @(NThunk m) @m t $ \case
        NVSet m -> pure $ Just m
        _ -> pure Nothing
    projectAttrSet t = force @(NValue m) @(NThunk m) @m t $ \case
        NVSet m -> pure m
        v -> throwError $ "Expected a set, but saw: " ++ show v

builtin :: Monad m => String -> (NThunk m -> m (NValue m)) -> m (NValue m)
builtin name f = return $ NVBuiltin name f

builtin2 :: Monad m
         => String -> (NThunk m -> NThunk m -> m (NValue m)) -> m (NValue m)
builtin2 name f = builtin name (builtin name . f)

builtin3 :: Monad m
         => String -> (NThunk m -> NThunk m -> NThunk m -> m (NValue m))
         -> m (NValue m)
builtin3 name f =
    builtin name $ \a -> builtin name $ \b -> builtin name $ \c -> f a b c

posFromSourcePos
    :: forall m v t.
        (MonadThunk v t m, AttrSetProjects m t,
         ConvertValue v Int, ConvertValue v Text,
         ConvertValue v (AttrSet t))
    => SourcePos -> m v
posFromSourcePos pos@(SourcePos f l c) =
    ofVal <$> attrsetFromList
        [ ([("file",   Just pos)], value @_ @_ @m $ ofVal (pack f))
        , ([("line",   Just pos)], value @_ @_ @m $ ofVal (unPos l))
        , ([("column", Just pos)], value @_ @_ @m $ ofVal (unPos c))
        ]

mkBoolV :: Monad m => Bool -> m (NValue m)
mkBoolV = return . NVConstant . NBool

mkIntV :: Monad m => Integer -> m (NValue m)
mkIntV = return . NVConstant . NInt

mkFloatV :: Monad m => Float -> m (NValue m)
mkFloatV = return . NVConstant . NFloat

isClosureNF :: Monad m => NValueNF m -> Bool
isClosureNF (Fix NVClosure {}) = True
isClosureNF _ = False

thunkEq :: (Framed e m, MonadFile m, MonadVar m,
           MonadThunk (NValue m) (NThunk m) m, Show (NValue m))
        => NThunk m -> NThunk m -> m Bool
thunkEq lt rt = force lt $ \lv -> force rt $ \rv -> valueEq lv rv

-- | Checks whether two containers are equal, using the given item equality
--   predicate. If there are any item slots that don't match between the two
--   containers, the result will be False.
alignEqM
    :: (Align f, Traversable f, Monad m)
    => (a -> b -> m Bool)
    -> f a
    -> f b
    -> m Bool
alignEqM eq fa fb = fmap (either (const False) (const True)) $ runExceptT $ do
    pairs <- forM (align fa fb) $ \case
        These a b -> return (a, b)
        _ -> throwE ()
    forM_ pairs $ \(a, b) -> guard =<< lift (eq a b)

isDerivation :: (Framed e m, MonadFile m, MonadVar m,
                MonadThunk (NValue m) (NThunk m) m, Show (NValue m))
             => AttrSet (NThunk m) -> m Bool
isDerivation m = case keyLookup "type" m of
    Just (Right t) -> force t $ valueEq (NVStr "derivation" mempty)
    _ -> pure False

valueEq :: (Framed e m, MonadFile m, MonadVar m,
           MonadThunk (NValue m) (NThunk m) m, Show (NValue m))
        => NValue m -> NValue m -> m Bool
valueEq l r = case (l, r) of
    (NVStr ls _, NVConstant (NUri ru)) -> pure $ ls == ru
    (NVConstant (NUri lu), NVStr rs _) -> pure $ lu == rs
    (NVConstant lc, NVConstant rc) -> pure $ lc == rc
    (NVStr ls _, NVStr rs _) -> pure $ ls == rs
    (NVStr ls _, NVConstant NNull) -> pure $ ls == ""
    (NVConstant NNull, NVStr rs _) -> pure $ "" == rs
    (NVList ls, NVList rs) -> alignEqM thunkEq ls rs
    (NVSet lm, NVSet rm) -> do
        let compareAttrs = attrsetCompare thunkEq lm rm
        isDerivation lm >>= \case
            True -> isDerivation rm >>= \case
                True -> case (keyLookup "outPath" lm,
                             keyLookup "outPath" rm) of
                           (Just (Right lp), Just (Right rp)) ->
                               thunkEq lp rp
                           _ -> compareAttrs
                _ -> compareAttrs
            _ -> compareAttrs
    (NVPath lp, NVPath rp) -> pure $ lp == rp
    _ -> pure False
