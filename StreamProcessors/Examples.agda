module StreamProcessors.Examples where

open import Codata.Thunk as Thunk using (Thunk; force)
open import Level using (Level)
open import Size

module RelationExamples where
  open import Data.Nat
  import Relation.Binary.PropositionalEquality as Eq

  open import StreamProcessors.Composition
  open import StreamProcessors.Core
  open import StreamProcessors.Functional
  import StreamProcessors.Relation
  open StreamProcessors.Relation.PropositionalEquality

  _ : ∀ {i} → i ⊢ map suc |> map suc ≈ map (λ n → suc (suc n))
  _ = helper
    where
    helper : ∀ {i : Size} → i ⊢ map suc |> map suc ≈ map (λ n → suc (suc n))
    helper = ≈demand λ _ → λ where .force → ≈lazyˡ λ where .force → ≈yield Eq.refl λ where .force → helper

module ProcessingExamples where
  open import Data.Empty.Polymorphic
  open import Data.List using (List; []; _∷_)
  open import Data.Nat
  open import Data.Nat.DivMod using (_%_)
  open import Data.Nat.Properties using (+-suc)
  open import Data.Vec as Vec using (Vec; []; _∷_)
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
  open Relation.Binary.PropositionalEquality.≡-Reasoning

  open import StreamProcessors.Composition
  open import StreamProcessors.Core
  open import StreamProcessors.Functional
  open import StreamProcessors.Processing

  fromVec : ∀ {i} {α} {A : Set α} {size : ℕ}
    → (xs : Vec A size)
    → Pipe ⊥ A i
  fromVec [] = stop
  fromVec (x ∷ xs) = yield x λ where .force → fromVec xs

  process-id : ∀ {α} {A : Set α} (size : ℕ) (xs : Vec A size)
    → process (size + size) (fromVec xs |> id) ≡ Vec.toList xs
  process-id 0 [] = refl
  process-id (suc size) (x ∷ xs) =
    begin
      process (suc size + suc size) (fromVec (x ∷ xs) |> id)
    ≡⟨⟩
      process (size + suc size) (fromVec xs |> id′ x)
    ≡⟨ cong (λ n → process n (fromVec xs |> id′ x)) (+-suc size size) ⟩
      process (suc (size + size)) (fromVec xs |> id′ x)
    ≡⟨⟩
      (x ∷ process (size + size) (fromVec xs |> id))
    ≡⟨ cong (x ∷_) (process-id size xs) ⟩
      Vec.toList (x ∷ xs)
    ∎

  _ : process 100 (fromVec (1 ∷ 2 ∷ 3 ∷ []) |> map (_+ 1)) ≡ 2 ∷ 3 ∷ 4 ∷ []
  _ = refl

  nats : ∀ {i} → Pipe ⊥ ℕ i
  natsFrom : ∀ {i} → ℕ → Pipe ⊥ ℕ i
  nats = natsFrom 0
  natsFrom n = yield n λ where .force → natsFrom (suc n)

  _ : process 100 (nats |> drop 5 |> filter (λ n → n % 2 ≡ᵇ 0) |> map (_* 2) |> take 3) ≡ 12 ∷ 16 ∷ 20 ∷ []
  _ = refl