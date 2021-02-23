module HsProof.ProofRef where

import           Control.Lens
import           Control.Monad                  ( void )
import           Control.Monad.Trans
import           Control.Monad.Trans.State
import           HsProof.Types

newProof l p = lift $ do
    ref <- get
    put $ ref & l %~ (++ [p])
    return $ ref ^. object & length

newProofObject :: Prop -> Proof ObjectId
newProofObject = newProof object

-- | create a new goal (append to last)
newGoal :: Prop -> Proof ()
newGoal = void . newProof goal

mutProof l i p = lift $ do
    ref <- get
    put $ ref & l . ix i .~ p

mutProofObject :: ObjectId -> Prop -> Proof ()
mutProofObject = mutProof object

-- | mutGoal should only mut the current goal
mutGoal :: Prop -> Proof ()
mutGoal = mutProof goal 0

-- | finish current goal (remove it from goal list)
finishGoal :: Proof ()
finishGoal = lift $ do
    ref <- get
    put $ ref & goal .~ tail (ref ^. goal)

getProofObject :: ObjectId -> Proof Prop
getProofObject i = lift $ do
    ref <- get
    return $ (ref ^. object) ^?! ix i

-- | copy a proof object
forkProofObject :: ObjectId -> Proof ObjectId
forkProofObject i = newProofObject =<< getProofObject i

newPropRef :: PropRef
newPropRef = PropRef [] []
