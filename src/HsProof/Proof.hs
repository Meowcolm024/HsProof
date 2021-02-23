{-# LANGUAGE FlexibleContexts #-}
module HsProof.Proof where

import           Control.Lens                   ( (^.) )
import           Control.Monad                  ( (>=>) )
import           Control.Monad.Except           ( runExceptT )
import           Control.Monad.Trans
import           Control.Monad.Trans.Except     ( except )
import           Control.Monad.Trans.State      ( get )
import           HsProof.ProofRef
import           HsProof.Types

-- | admit
admitted :: Proof a
admitted = except $ Left Proved

-- | finish the proof 
qed :: Proof a
qed = do
    ref <- lift get
    except $ case _goal ref of
        []      -> Left Proved
        (x : _) -> Left (Failed x)

-- | abort the proof and return current goal
abort :: Proof a
abort = do
    ref <- lift get
    except $ case _goal ref of
        []      -> Left (Failed None)
        (x : _) -> Left (Failed x)

-- | show all proof content
status :: Proof PropRef
status = lift get >>= except . Right

-- | exfalso: F -> anything
exfalso :: ObjectId -> Proof ()
exfalso i = do
    ref <- lift get
    k   <- getProofObject i
    case k of
        F -> finishGoal
        x -> except $ Left (Failed x)

-- | apply theorem/prop to the goal
apply' :: Appliable a Prop => a -> Proof ()
apply' p = do
    ref <- lift get
    case app p . head . _goal $ ref of
        Left  Proved      -> finishGoal
        Left  (Failed p') -> except $ Left (Failed p')
        Right p'          -> mutGoal p'

-- | same as apply', but using ObjectId
apply :: ObjectId -> Proof ()
apply i = apply' =<< getProofObject i

-- | apply to multiple props and create a new prop object
applyToM :: Appliable a [Prop] => a -> [ObjectId] -> Proof ObjectId
applyToM p is = do
    ref <- lift get
    ks  <- mapM getProofObject is
    case app p ks of
        Right p' -> newProofObject p'
        Left  f  -> except (Left f)

-- | <applyM>, but modify one instead of creating a new one
applyToM' :: Appliable a [Prop] => a -> [ObjectId] -> ObjectId -> Proof ()
applyToM' t ps o = t `applyToM` ps >>= getProofObject >>= mutProofObject o

-- | apply to a <Prop>
applyTo' :: Appliable a Prop => a -> ObjectId -> Proof ()
applyTo' p i = do
    ref <- lift get
    k   <- getProofObject i
    case app p k of
        Right p' -> mutProofObject i p'
        Left  f  -> except (Left f)

-- | same as <applyTo'>, but using <ObjectId>
applyTo :: ObjectId -> ObjectId -> Proof ()
applyTo t p = flip applyTo' p =<< getProofObject t

-- | like intro in coq
intro :: Proof ObjectId
intro = do
    ref <- lift get
    case ref ^. goal of
        (x : _) -> case x of
            (p :-> q) -> mutGoal q >> newProofObject p
            _         -> except $ Left (Failed x)
        _ -> except $ Left (Failed None)

-- | applyTo acts differently, so we need a separate method
imply :: Theorem'
imply [t@(p :->  q), h] = if p == h then Right q else Left $ Failed t
imply [t@(_ :<-> _), h] = app t h
imply _                 = Left $ Failed None

-- | lift a <Prop> to <Theorem> using ObjectId
theorem' :: ObjectId -> Proof Theorem
theorem' i = do
    ref <- lift get
    obj <- getProofObject i
    return $ theorem obj

-- | lifts a <Prop> to <Theorem>
theorem :: Prop -> Theorem
theorem t@(p :->  q) h = imply [t, h]
theorem t@(p :<-> q) h = imply [t, h]
theorem _            _ = Left $ Failed None

-- | lifted (>=>) combining theorems: (a -> b) -> (b -> c) => (a -> c)
(>$>) :: ObjectId -> ObjectId -> Proof Theorem
p >$> q = (>=>) <$> theorem' p <*> theorem' q
