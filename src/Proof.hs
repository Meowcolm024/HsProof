{-# LANGUAGE FlexibleContexts #-}
module Proof where

import           Control.Monad.Trans
import           Control.Monad.Trans.Except     ( except )
import           Control.Monad.Trans.State
import           ProofRef
import           Types

-- | finish the proof 
qed :: Proof Prop
qed = do
    ref <- lift get
    except $ case _goal ref of
        []      -> Left Proved
        (x : _) -> Left (Failed x)

-- | abort the proof and return current goal
abort :: Proof Prop
abort = do
    ref <- lift get
    except $ case _goal ref of
        []      -> Left (Failed None)
        (x : _) -> Left (Failed x)

exfalso :: ObjectId -> Proof ()
exfalso i = do
    ref <- lift get
    k   <- getProofObject i
    case k of
        F -> finishGoal
        x -> except $ Left (Failed x)

-- | apply to the goal
apply' :: Appliable a Prop => a -> Proof ()
apply' p = do
    ref <- lift get
    case app p . head . _goal $ ref of
        Left  Proved      -> finishGoal
        Left  (Failed p') -> except $ Left (Failed p')
        Right p'          -> mutGoal 0 p'

-- | same as apply', but using ObjectId
apply :: ObjectId -> Proof ()
apply i = apply' =<< getProofObject i

-- | apply to multiple props
applyToM' :: Appliable a [Prop] => a -> [ObjectId] -> Proof ObjectId
applyToM' p is = do
    ref <- lift get
    ks  <- mapM getProofObject is
    case app p ks of
        Right p' -> newProofObject p'
        Left  f  -> except (Left f)

-- applyToM :: ObjectId -> [ObjectId] -> Proof Prop 
-- applyToM t ps = flip applyToM' ps =<< getProofObject t

-- | apply to a prop
applyTo' :: Appliable a Prop => a -> ObjectId -> Proof ()
applyTo' p i = do
    ref <- lift get
    k   <- getProofObject i
    case app p k of
        Right p' -> mutProofObject i p'
        Left  f  -> except (Left f)

-- | same as applyTo', but using ObjectId
applyTo :: ObjectId -> ObjectId -> Proof ()
applyTo t p = flip applyTo' p =<< getProofObject t
