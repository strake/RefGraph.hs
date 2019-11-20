{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures -Wno-simplifiable-class-constraints #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=256 #-}
module Data.RefGraph (traversePost, traversePost', traversePre, traversePre') where

import           Prelude hiding ((.), (<$>), Functor, id, map)
import           Control.Category
import           Control.Categorical.Functor (Endofunctor, Functor (..), NT (..), (<$>))
import           Control.Categorical.Monad (Kleisli (..), (>=>))
import           Control.Lens (fstL)
import           Control.Monad.Trans.Class (MonadTrans (..))
import           Control.Monad.Trans.Except (ExceptT (..), runExceptT)
import           Control.Monad.Trans.Key (Key, KeyringT, newKey)
import           Control.Monad.Trans.Maybe (MaybeT (..), maybeToExceptT)
import           Control.Monad.Trans.Reader (ReaderT (..), mapReaderT)
import           Control.Monad.Trans.State (StateT (..))
import qualified Control.Monad.Trans.State as M
import           Data.Maybe (fromMaybe)
import           Data.Vault (Vault)
import qualified Data.Vault as Vault
import           Lens.Micro.Mtl (zoom)

traversePost
 :: (Monad m, _)
 => KNT (->) (RGMT t b m) (a (Key t)) (b (Key t))
 -> KNT (->) (ReaderT (RGV s a) (RGMT t b m)) (Key s) (Key t)
traversePost f = mapKNT (NT (mapReaderT unhelp)) go where
    go :: _ (_ :: κ -> _) (_ :: κ -> _)
    go = xformKNT helper $ mapKNT (NT (lift . zoom fstL)) f . map go

traversePost'
 :: (Monad m, _)
 => KNT (->) (MaybeT (RGMT s a m)) (a (Key s)) (a (Key s))
 -> KNT (->) (RGMT s a m) (Key s) (Key s)
traversePost' f = mapKNT (NT unhelp) go where
    go = xformKNT helper' $ mapKNT (NT (zoom fstL)) f . mapKNT (NT lift) (map go)

traversePre
 :: (Monad m, _)
 => KNT (->) (RGMT t b m) (a (Key s)) (b (Key s))
 -> KNT (->) (ReaderT (RGV s a) (RGMT t b m)) (Key s) (Key t)
traversePre f = mapKNT (NT (mapReaderT unhelp)) go where
    go :: _ (_ :: κ -> _) (_ :: κ -> _)
    go = xformKNT helper $ map go . mapKNT (NT (lift . zoom fstL)) f

traversePre'
 :: (Monad m, _)
 => KNT (->) (MaybeT (RGMT s a m)) (a (Key s)) (a (Key s))
 -> KNT (->) (RGMT s a m) (Key s) (Key s)
traversePre' f = mapKNT (NT unhelp) go where
    go = xformKNT helper' $ mapKNT (NT lift) (map go) . mapKNT (NT (zoom fstL)) f

helper
 :: (Monad m)
 => (a (Key s) k -> ReaderT (RGV s a) (StateT (Vault t (b (Key t)), Vault s (Key t)) (KeyringT t m)) (b (Key t) k))
 -> Key s k -> ReaderT (RGV s a) (StateT (Vault t (b (Key t)), Vault s (Key _)) (KeyringT t m)) (Key t k)
helper φ = fmap ReaderT . flip $ \ vault ->
    helper'' (lift . flip runReaderT vault . φ . unRefGraph . RefGraph vault)

helper'
 :: (Monad m)
 => (a (Key s) k -> MaybeT (StateT (RGV s a, Vault s (Key s)) (KeyringT s m)) (a (Key s) k))
 -> (Key s k -> StateT (RGV s a, Vault s (Key _)) (KeyringT s m) (Key s k))
helper' φ = \ key -> do
    (vault, _) <- M.get
    helper'' (maybeToExceptT <*> φ . unRefGraph . RefGraph vault) key

helper''
 :: (Monad m)
 => (Key s k -> ExceptT (Key t k) (StateT (Vault t (b (Key t)), Vault s (Key t)) (KeyringT t m)) (b (Key t) k))
 -> Key s k -> StateT (Vault t (b (Key t)), Vault s (Key _)) (KeyringT t m) (Key t k)
helper'' φ = \ key -> do (_, memos) <- M.get; maybe (go key) pure $ memos Vault.!? key
  where go = runExceptT . φ >=> \ case
            Left key' -> pure key'
            Right root' -> zoom fstL (newNode root')

unhelp :: _ => StateT (σ, Vault s z) f a -> StateT σ f a
unhelp = map fst . flip splitStateR Vault.empty

newNode :: (Monad m) => a k -> StateT (Vault s a) (KeyringT s m) (Key s k)
newNode node = do
    key <- lift newKey
    key <$ M.modify (Vault.insertWith pure key node)

data RefGraph s a k = RefGraph (RGV s a) (Key s k)

unRefGraph :: RefGraph s a k -> a (Key s) k
unRefGraph (RefGraph vault key) =
    fromMaybe (error "bad `RefGraph`") $ vault Vault.!? key

type RGV s a = Vault s (a (Key s))
type RGMT s a m = StateT (RGV s a) (KeyringT s m)
type KNT s m = NT (Kleisli s m)

mapKNT :: Category s => NT s m n -> KNT s m a b -> KNT s n a b
mapKNT f a = NT (Kleisli (nt f . kleisli (nt a)))

xformKNT :: (∀ k . s (a k) (m (b k)) -> t (α k) (n (β k))) -> KNT s m a b -> KNT t n α β
xformKNT φ f = NT (Kleisli (φ (kleisli (nt f))))

splitStateR :: Endofunctor (->) f => StateT (s, t) f a -> t -> StateT s f (a, t)
splitStateR (StateT x) t = StateT (\ s -> (\ (a, (s, t)) -> ((a, t), s)) <$> x (s, t))
