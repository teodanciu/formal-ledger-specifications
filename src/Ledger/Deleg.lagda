\section{Delegation}

\begin{code}[hide]
{-# OPTIONS --safe #-}

open import Ledger.Prelude
open import Ledger.GovStructure

module Ledger.Deleg (gs : _) (open GovStructure gs) where

open import Ledger.GovernanceActions gs hiding (yes; no)

\end{code}
\begin{figure*}[h]
\begin{code}
record PoolParams : Set where
  field rewardAddr : Credential

data DCert : Set where
  delegate    : Credential → Maybe VDeleg → Maybe Credential → Coin → DCert
  regpool     : Credential → PoolParams → DCert
  retirepool  : Credential → Epoch → DCert
  regdrep     : Credential → Coin → Anchor → DCert
  deregdrep   : Credential → DCert
  ccreghot    : Credential → Maybe Credential → DCert

record CertEnv : Set where
  constructor ⟦_,_,_⟧ᶜ
  field epoch  : Epoch
        pp     : PParams
        votes  : List GovVote

record DState : Set where
  constructor ⟦_,_,_⟧ᵈ
  field
    voteDelegs   : Credential ⇀ VDeleg      -- stake credential to DRep credential
    stakeDelegs  : Credential ⇀ Credential  -- stake credential to pool credential
    rewards      : RwdAddr ⇀ Coin

record PState : Set where
  constructor ⟦_,_⟧ᵖ
  field pools     : Credential ⇀ PoolParams
        retiring  : Credential ⇀ Epoch

record GState : Set where
  constructor ⟦_,_⟧ᵛ
  field dreps      : Credential ⇀ Epoch
        ccHotKeys  : Credential ⇀ Maybe Credential

record CertState : Set where
  constructor ⟦_,_,_⟧ᶜ
  field dState : DState
        pState : PState
        gState : GState

GovCertEnv  = CertEnv
DelegEnv    = PParams
PoolEnv     = PParams
\end{code}
\caption{Types used for CERTS transition system}
\end{figure*}

\begin{figure*}[h]
\begin{code}[hide]
private variable
  an : Anchor
  dReps dReps' : Credential ⇀ Epoch
  pools : Credential ⇀ PoolParams
  vDelegs : Credential ⇀ VDeleg
  sDelegs : Credential ⇀ Credential
  retiring retiring' : Credential ⇀ Epoch
  ccKeys : Credential ⇀ Maybe Credential
  rwds : RwdAddr ⇀ Coin
  dCert : DCert
  c c' : Credential
  mc : Maybe Credential
  mv : Maybe VDeleg
  d : Coin
  e : Epoch
  kh kh' : KeyHash
  mkh : Maybe KeyHash
  st st' : CertState
  stᵍ stᵍ' : GState
  stᵈ stᵈ' : DState
  stᵖ stᵖ' : PState
  Γ : CertEnv
  pp : PParams
  vs : List GovVote
  poolParams : PoolParams

module _ (open PParams) where
\end{code}
\begin{code}
  cwitness : DCert → Credential
  cwitness (delegate c _ _ _)  = c
  cwitness (regpool c _)       = c
  cwitness (retirepool c _)    = c
  cwitness (regdrep c _ _)     = c
  cwitness (deregdrep c)       = c
  cwitness (ccreghot c _)      = c

  requiredDeposit : {A : Set} → PParams → Maybe A → Coin
  requiredDeposit pp (just _)  = pp .poolDeposit
  requiredDeposit pp nothing   = 0

  getDRepVote : GovVote → Maybe Credential
  getDRepVote record { role = DRep ; credential = credential }  = just credential
  getDRepVote _                                                 = nothing
\end{code}
\caption{Functions used for CERTS transition system}
\end{figure*}

\begin{figure*}[h]
\begin{code}
data _⊢_⇀⦇_,DELEG⦈_ : DelegEnv → DState → DCert → DState → Set where
  DELEG-delegate :
    d ≡ requiredDeposit pp mv ⊔ requiredDeposit pp mc
    ────────────────────────────────
    pp ⊢  ⟦ vDelegs , sDelegs , rwds ⟧ᵈ ⇀⦇ delegate c mv mc d ,DELEG⦈
          ⟦ insertIfJust c mv vDelegs , insertIfJust c mc sDelegs , rwds ⟧ᵈ

data _⊢_⇀⦇_,POOL⦈_ : PoolEnv → PState → DCert → PState → Set where
  POOL-regpool : let open PParams pp ; open PoolParams poolParams in
    c ∉ dom pools
    ────────────────────────────────
    pp ⊢  ⟦ pools , retiring ⟧ᵖ ⇀⦇ regpool c poolParams ,POOL⦈
          ⟦ ❴ c , poolParams ❵ᵐ ∪ᵐˡ pools , retiring ⟧ᵖ

  POOL-retirepool :
    pp ⊢  ⟦ pools , retiring ⟧ᵖ ⇀⦇ retirepool c e ,POOL⦈
          ⟦ pools , ❴ c , e ❵ᵐ ∪ᵐˡ retiring ⟧ᵖ

data _⊢_⇀⦇_,GOVCERT⦈_ : GovCertEnv → GState → DCert → GState → Set where
  GOVCERT-regdrep : let open PParams pp in
    (d ≡ drepDeposit × c ∉ dom dReps) ⊎ (d ≡ 0 × c ∈ dom dReps)
    ────────────────────────────────
    ⟦ e , pp , vs ⟧ᶜ ⊢  ⟦ dReps , ccKeys ⟧ᵛ ⇀⦇ regdrep c d an ,GOVCERT⦈
                        ⟦ ❴ c , e + drepActivity ❵ᵐ ∪ᵐˡ dReps , ccKeys ⟧ᵛ

  GOVCERT-deregdrep :
    c ∈ dom dReps
    ────────────────────────────────
    Γ ⊢  ⟦ dReps , ccKeys ⟧ᵛ ⇀⦇ deregdrep c ,GOVCERT⦈
         ⟦ dReps ∣ ❴ c ❵ ᶜ , ccKeys ⟧ᵛ

  GOVCERT-ccreghot :
    (c , nothing) ∉ ccKeys
    ────────────────────────────────
    Γ ⊢  ⟦ dReps , ccKeys ⟧ᵛ ⇀⦇ ccreghot c mc ,GOVCERT⦈
         ⟦ dReps , singletonᵐ c mc ∪ᵐˡ ccKeys ⟧ᵛ
\end{code}
\caption{Auxiliary DELEG and POOL rules}
\end{figure*}

\begin{figure*}[h]
\begin{code}
data _⊢_⇀⦇_,CERT⦈_ : CertEnv → CertState → DCert → CertState → Set where
  CERT-deleg :
    pp ⊢ stᵈ ⇀⦇ dCert ,DELEG⦈ stᵈ'
    ────────────────────────────────
    ⟦ e , pp , vs ⟧ᶜ ⊢ ⟦ stᵈ , stᵖ , stᵍ ⟧ᶜ ⇀⦇ dCert ,CERT⦈ ⟦ stᵈ' , stᵖ , stᵍ ⟧ᶜ

  CERT-pool :
    pp ⊢ stᵖ ⇀⦇ dCert ,POOL⦈ stᵖ'
    ────────────────────────────────
    ⟦ e , pp , vs ⟧ᶜ ⊢ ⟦ stᵈ , stᵖ , stᵍ ⟧ᶜ ⇀⦇ dCert ,CERT⦈ ⟦ stᵈ , stᵖ' , stᵍ ⟧ᶜ

  CERT-vdel :
    Γ ⊢ stᵍ ⇀⦇ dCert ,GOVCERT⦈ stᵍ'
    ────────────────────────────────
    Γ ⊢ ⟦ stᵈ , stᵖ , stᵍ ⟧ᶜ ⇀⦇ dCert ,CERT⦈ ⟦ stᵈ , stᵖ , stᵍ' ⟧ᶜ

data _⊢_⇀⦇_,CERTBASE⦈_ : CertEnv → CertState → ⊤ → CertState → Set where
  CERT-base :
    let open PParams pp; open CertState st; open GState gState
        refresh = mapPartial getDRepVote (fromList vs)
    in ⊤ -- TODO: check that the withdrawals are correct here
    ────────────────────────────────
    ⟦ e , pp , vs ⟧ᶜ ⊢ st ⇀⦇ _ ,CERTBASE⦈ record st
      { gState = record gState
        { dreps = mapValueRestricted (const (e + drepActivity)) dreps refresh } }

_⊢_⇀⦇_,CERTS⦈_ : CertEnv → CertState → List DCert → CertState → Set
_⊢_⇀⦇_,CERTS⦈_ = SS⇒BSᵇ _⊢_⇀⦇_,CERTBASE⦈_ _⊢_⇀⦇_,CERT⦈_
\end{code}
\caption{CERTS rules}
\end{figure*}

\begin{code}[hide]
open import Data.Maybe.Properties
open import Relation.Nullary.Decidable

open import Tactic.ReduceDec

open Computational ⦃...⦄

instance
  Computational-DELEG : Computational _⊢_⇀⦇_,DELEG⦈_
  Computational-DELEG .computeProof pp _ = λ where
    (delegate c mv mc d) →
      case d ≟ requiredDeposit pp mv ⊔ requiredDeposit pp mc of λ where
        (yes p) → just (-, DELEG-delegate p)
        (no _)  → nothing
    _ → nothing
  Computational-DELEG .completeness pp s (delegate c mv mc d) s' (DELEG-delegate p)
    rewrite dec-yes (d ≟ requiredDeposit pp mv ⊔ requiredDeposit pp mc) p .proj₂ = refl

instance
  Computational-POOL : Computational _⊢_⇀⦇_,POOL⦈_
  Computational-POOL .computeProof _ ⟦ pools , _ ⟧ᵖ (regpool c _) =
    case c ∈? dom pools of λ where
      (yes _) → nothing
      (no p)  →  just (-, POOL-regpool p)
  Computational-POOL .computeProof _ _ (retirepool c e) = just (-, POOL-retirepool)
  Computational-POOL .computeProof _ _ _ = nothing
  Computational-POOL .completeness _ ⟦ pools , _ ⟧ᵖ (regpool c _) _ (POOL-regpool ¬p)
    rewrite dec-no (c ∈? dom pools) ¬p = refl
  Computational-POOL .completeness _ _ (retirepool _ _) _ POOL-retirepool = refl

  Computational-GOVCERT : Computational _⊢_⇀⦇_,GOVCERT⦈_
  Computational-GOVCERT .computeProof ⟦ _ , pp , _ ⟧ᶜ ⟦ dReps , _ ⟧ᵛ (regdrep c d _) =
    let open PParams pp in
    case ¿ (d ≡ drepDeposit × c ∉ dom dReps)
         ⊎ (d ≡ 0 × c ∈ dom dReps) ¿ of λ where
      (yes p) → just (-, GOVCERT-regdrep p)
      (no _)  → nothing
  Computational-GOVCERT .computeProof _ ⟦ dReps , _ ⟧ᵛ (deregdrep c) =
    case c ∈? dom dReps of λ where
      (yes p) → just (-, GOVCERT-deregdrep p)
      (no _)  → nothing
  Computational-GOVCERT .computeProof _ ⟦ _ , ccKeys ⟧ᵛ (ccreghot c _) =
    case (c , nothing) ∈? (ccKeys ˢ) of λ where
      (yes _) → nothing
      (no p)  → just (-, GOVCERT-ccreghot p)
  Computational-GOVCERT .computeProof _ _ _ = nothing
  Computational-GOVCERT .completeness ⟦ _ , pp , _ ⟧ᶜ ⟦ dReps , _ ⟧ᵛ
    (regdrep c d _) _ (GOVCERT-regdrep p)
    rewrite dec-yes
      ¿ (let open PParams pp in
        (d ≡ drepDeposit × c ∉ dom dReps) ⊎ (d ≡ 0 × c ∈ dom dReps))
      ¿ p .proj₂ = refl
  Computational-GOVCERT .completeness _ ⟦ dReps , _ ⟧ᵛ
    (deregdrep c) _ (GOVCERT-deregdrep p)
    rewrite dec-yes (c ∈? dom dReps) p .proj₂ = refl
  Computational-GOVCERT .completeness _ ⟦ _ , ccKeys ⟧ᵛ
    (ccreghot c _) _ (GOVCERT-ccreghot ¬p)
    rewrite dec-no ((c , nothing) ∈? (ccKeys ˢ)) ¬p = refl

instance
  Computational-CERT : Computational _⊢_⇀⦇_,CERT⦈_
  Computational-CERT .computeProof Γ@(⟦ e , pp , vs ⟧ᶜ) ⟦ stᵈ , stᵖ , stᵍ ⟧ᶜ dCert
    with computeProof pp stᵈ dCert | computeProof pp stᵖ dCert | computeProof Γ stᵍ dCert
  ... | just (_ , h) | _            | _            = just (-, CERT-deleg h)
  ... | nothing      | just (_ , h) | _            = just (-, CERT-pool h)
  ... | nothing      | nothing      | just (_ , h) = just (-, CERT-vdel h)
  ... | nothing      | nothing      | nothing      = nothing
  Computational-CERT .completeness ⟦ _ , pp , _ ⟧ᶜ ⟦ stᵈ , stᵖ , stᵍ ⟧ᶜ
    dCert@(delegate c mv mc d) ⟦ stᵈ' , stᵖ , stᵍ ⟧ᶜ (CERT-deleg h)
    with computeProof pp stᵈ dCert | completeness _ _ _ _ h
  ... | just _ | refl = refl
  Computational-CERT .completeness ⟦ _ , pp , _ ⟧ᶜ ⟦ stᵈ , stᵖ , stᵍ ⟧ᶜ
    dCert@(regpool c poolParams) ⟦ stᵈ , stᵖ' , stᵍ ⟧ᶜ (CERT-pool h)
    with computeProof pp stᵖ dCert | completeness _ _ _ _ h
  ... | just _ | refl = refl
  Computational-CERT .completeness ⟦ _ , pp , _ ⟧ᶜ ⟦ stᵈ , stᵖ , stᵍ ⟧ᶜ
    dCert@(retirepool c e) ⟦ stᵈ , stᵖ' , stᵍ ⟧ᶜ (CERT-pool h)
    with completeness _ _ _ _ h
  ... | refl = refl
  Computational-CERT .completeness Γ ⟦ stᵈ , stᵖ , stᵍ ⟧ᶜ
    dCert@(regdrep c d an)
    ⟦ stᵈ , stᵖ , stᵍ' ⟧ᶜ (CERT-vdel h)
    with computeProof Γ stᵍ dCert | completeness _ _ _ _ h
  ... | just _ | refl = refl
  Computational-CERT .completeness Γ ⟦ stᵈ , stᵖ , stᵍ ⟧ᶜ
    dCert@(deregdrep c) ⟦ stᵈ , stᵖ , stᵍ' ⟧ᶜ (CERT-vdel h)
    with computeProof Γ stᵍ dCert | completeness _ _ _ _ h
  ... | just _ | refl = refl
  Computational-CERT .completeness Γ ⟦ stᵈ , stᵖ , stᵍ ⟧ᶜ
    dCert@(ccreghot c mkh) ⟦ stᵈ , stᵖ , stᵍ' ⟧ᶜ (CERT-vdel h)
    with computeProof Γ stᵍ dCert | completeness _ _ _ _ h
  ... | just _ | refl = refl

  Computational-CERTBASE : Computational _⊢_⇀⦇_,CERTBASE⦈_
  Computational-CERTBASE .computeProof ⟦ e , pp , vs ⟧ᶜ st _ = just (-, CERT-base _)
  Computational-CERTBASE .completeness ⟦ e , pp , vs ⟧ᶜ st _ st' (CERT-base _) = refl

Computational-CERTS : Computational _⊢_⇀⦇_,CERTS⦈_
Computational-CERTS = it
\end{code}
