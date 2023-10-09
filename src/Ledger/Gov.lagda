\section{Governance}

\begin{code}[hide]
{-# OPTIONS --safe #-}
import Data.List as L
open import Relation.Nullary.Decidable

open import Ledger.Prelude hiding (yes; no)
open import Ledger.Crypto
open import Ledger.GovStructure

module Ledger.Gov (⋯ : _) (open GovStructure ⋯ hiding (epoch)) where

open import Ledger.GovernanceActions ⋯
\end{code}
\begin{figure*}[h]
\begin{code}
record GovActionState : Set where
  field votes       : (GovRole × Credential) ⇀ Vote
        returnAddr  : RwdAddr
        expiresIn   : Epoch
        action      : GovAction
        prevAction  : NeedsHash action

GovState : Set
GovState = List (GovActionID × GovActionState)

record GovEnv : Set where
  constructor ⟦_,_,_⟧ᵗ
  field txid     : TxId
        epoch    : Epoch
        pparams  : PParams
\end{code}
\begin{code}[hide]
open GovActionState

private variable
  Γ : GovEnv
  s s' : GovState
  aid : GovActionID
  role : GovRole
  cred : Credential
  v : Vote
  c d : Coin
  addr : RwdAddr
  a : GovAction
  prev : NeedsHash a
\end{code}
\begin{code}
-- could be implemented using a function of type:
--   ∀ {a} {A : Set a} → (A → Maybe A) → List A → List A
modifyMatch : ∀ {a} {A : Set a} → (A → Bool) → (A → A) → List A → List A
modifyMatch P f = L.map (λ x → if P x then f x else x)

addVote : GovState → GovActionID → GovRole → Credential → Vote → GovState
addVote s aid r kh v =
  modifyMatch
    (λ x → ⌊ aid ≟ proj₁ x ⌋)
    (λ (gid , s') → gid , record s' { votes = insert (votes s') (r , kh) v }) s

addAction : GovState
          → Epoch → GovActionID → RwdAddr → (a : GovAction) → NeedsHash a
          → GovState
addAction s e aid addr a prev = s ∷ʳ (aid , record
  { votes = ∅ᵐ ; returnAddr = addr ; expiresIn = e ; action = a ; prevAction = prev })

-- x is the anchor in those two cases, which we don't do anything with
data _⊢_⇀⦇_,GOV'⦈_ : GovEnv × ℕ → GovState → GovVote ⊎ GovProposal → GovState → Set where

  GOV-Vote : ∀ {x k ast} → let open GovEnv Γ in
    (aid , ast) ∈ setFromList s
    → canVote pparams (action ast) role
    ────────────────────────────────
    let sig = inj₁ record { gid = aid ; role = role ; credential = cred
                          ; vote = v ; anchor = x }
    in (Γ , k) ⊢ s ⇀⦇ sig ,GOV'⦈ addVote s aid role cred v

  GOV-Propose : ∀ {x k} (open GovEnv Γ) →
    let open PParams pparams using (govExpiration; govDeposit) in
    actionWellFormed a ≡ true
    → d ≡ govDeposit
    ────────────────────────────────
    let sig = inj₂ record { returnAddr = addr ; action = a ; anchor = x
                          ; deposit = d ; prevAction = prev }
        s'  = addAction s (govExpiration +ᵉ epoch) (txid , k) addr a prev
    in
    (Γ , k) ⊢ s ⇀⦇ sig ,GOV'⦈ s'

_⊢_⇀⦇_,GOV⦈_ : GovEnv → GovState → List (GovVote ⊎ GovProposal) → GovState → Set
_⊢_⇀⦇_,GOV⦈_ = SS⇒BS (λ Γ → Γ ⊢_⇀⦇_,GOV'⦈_)
\end{code}
\caption{TALLY types}
\label{defs:tally-types}
\end{figure*}
