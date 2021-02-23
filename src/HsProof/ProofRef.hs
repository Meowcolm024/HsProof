module HsProof.ProofRef where

import           Control.Lens
import           Control.Monad                  ( void )
import           Control.Monad.Trans
import           Control.Monad.Trans.State
import           HsProof.Types

-- | abstract function for creating a new proof object
newProof l p = lift $ do
    ref <- get
    put $ ref & l %~ (++ [p])
    return $ ref ^. object & length

-- | create a new proof object
newProofObject :: Prop -> Proof ObjectId
newProofObject = newProof object

-- | create a new goal (append to last)
newGoal :: Prop -> Proof ()
newGoal = void . newProof goal

-- | abstract function for mutating a proof object
mutProof l i p = lift $ do
    ref <- get
    put $ ref & l . ix i .~ p

-- | mut a proof object
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

-- | return the Prop using <ObjectId>
getProofObject :: ObjectId -> Proof Prop
getProofObject i = lift $ do
    ref <- get
    return $ (ref ^. object) ^?! ix i

-- | copy a proof object
forkProofObject :: ObjectId -> Proof ObjectId
forkProofObject i = newProofObject =<< getProofObject i

-- | emty env
newPropRef :: PropRef
newPropRef = PropRef [] []
