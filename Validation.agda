module Validation where

open import Data.Fin using (Fin; zero; suc; inject₁)
open import Data.Fin.Properties renaming (_≟_ to _≟Fin_)
open import Data.List as List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (∃; ∃₂; _×_; _,_; ,_; proj₁; proj₂; uncurry)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Vec.All using (all)
open import Data.Maybe using (Maybe; just; nothing)
open import Function
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst; inspect; [_])
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness)

open import Game

open Card

search : ∀ {A : Set} {{x}} → A
search {{x}} = x

searchWith : ∀ {A : Set} (A? : Dec A) {{x : True A?}} → A
searchWith _ {{x}} = toWitness x

infixr 6 _≟Color_
_≟Color_ : (c c′ : Color) → Dec (c ≡ c′)
red ≟Color red = yes refl
red ≟Color black = no λ ()
black ≟Color red = no λ ()
black ≟Color black = yes refl

infixr 6 _≟Suit_
_≟Suit_ : ∀ {c} (s s′ : Suit c) → Dec (s ≡ s′)
♥ ≟Suit ♥ = yes refl
♥ ≟Suit ♢ = no λ ()
♢ ≟Suit ♥ = no λ ()
♢ ≟Suit ♢ = yes refl
♠ ≟Suit ♠ = yes refl
♠ ≟Suit ♣ = no λ ()
♣ ≟Suit ♠ = no λ ()
♣ ≟Suit ♣ = yes refl

infixr 6 _+1≡_
data _+1≡_ : ∀ {n} → Fin n → Fin n → Set where
  zero : ∀ {n} → zero {suc n} +1≡ suc zero
  suc : ∀ {n} {i i′ : Fin n} → i +1≡ i′ → suc i +1≡ suc i′

+1≡-refl : ∀ {n} {i : Fin n} → inject₁ i +1≡ suc i
+1≡-refl {i = ace} = zero
+1≡-refl {i = suc _} = suc +1≡-refl

+1≡-inject : ∀ {n} {i i′ : Fin (suc n)} →
  i +1≡ i′ → ∃ λ j → inject₁ j ≡ i × suc j ≡ i′
+1≡-inject zero = , refl , refl
+1≡-inject (suc zero) = , refl , refl
+1≡-inject (suc p@(suc _)) =
  let (j , p , q) = +1≡-inject p in
    , cong suc p , cong suc q

infixr 6 _+1≟_
_+1≟_ : ∀ {n} (i j : Fin n) → Dec (i +1≡ j)
ace +1≟ ace = no λ ()
ace +1≟ two = yes zero
ace +1≟ suc (suc j) = no λ ()
suc i +1≟ ace = no λ ()
suc i +1≟ suc j with i +1≟ j
… | yes p = yes (suc p)
… | no ¬p = no λ where (suc p) → ¬p p

pileRule? : ∀ pt cd cd′ → Dec (PileRule pt (touch cd) cd′)
pileRule? cascade cd (just cd′)
  with otherColor (color cd) ≟Color color cd′
pileRule? cascade cd (just cd′)
  | yes refl with rank cd +1≟ rank cd′
pileRule? cascade cd (just cd′@(_ of _ is _))
  | yes refl | yes p with +1≡-inject p
pileRule? cascade cd (just cd′@(_ of _ is _))
  | yes refl | yes p | _ , refl , refl = yes movedCons
pileRule? cascade cd (just cd′@(_ of _ is _))
  | yes refl | no ¬p = no λ where movedCons → ¬p +1≡-refl
pileRule? cascade cd (just cd′@(_ of _ is _))
  | no ¬p = no λ where movedCons → ¬p refl
pileRule? cascade cd nothing with rank cd ≟Fin king
… | yes refl = yes movedStart
… | no ¬p = no λ where movedStart → ¬p refl
pileRule? foundation cd nothing with rank cd ≟Fin ace
… | yes refl = yes start
… | no ¬p = no λ where start → ¬p refl
pileRule? foundation cd (just cd′)
  with color cd ≟Color color cd′
pileRule? foundation cd (just cd′@(_ of _ is _))
  | yes refl with rank cd′ +1≟ rank cd
pileRule? foundation cd (just cd′@(_ of _ is _))
  | yes refl | yes p with +1≡-inject p
pileRule? foundation cd@(_ of _ is _) (just cd′@(_ of _ is _))
  | yes refl | yes p | _ , refl , refl with suit cd ≟Suit suit cd′
pileRule? foundation cd@(_ of _ is _) (just cd′@(_ of _ is _))
  | yes refl | yes p | _ , refl , refl | yes refl = yes cons
pileRule? foundation cd@(_ of _ is _) (just cd′@(_ of _ is _))
  | yes refl | yes p | _ , refl , refl | no s≢s′ = no λ where cons → s≢s′ refl
pileRule? foundation cd@(_ of _ is _) (just cd′@(_ of _ is _))
  | yes refl | no ¬p = no λ where cons → ¬p +1≡-refl
pileRule? foundation cd (just cd′)
  | no c≢c′ = no λ where cons → c≢c′ refl
pileRule? cell cd (just _) = no λ ()
pileRule? cell cd nothing = yes start

_▹?_ : ∀ {pt pt′ cds cds′}
  (p : Pile pt cds) (p′ : Pile pt′ cds′) → Dec (p ▹ p′)
[] ▹? p′ = no λ ()
_▹?_ {cds = cd ∷ _} (_ ∷ p) p′ = case pileRule? _ (touch cd) _ of λ where
  (yes pr) → yes (move pr)
  (no ¬pr) → no λ where (move pr) → ¬pr pr

_▸?_ : ∀ {n i pt pt′ cd cds cds′} {g : Game n}
  (l : Location g i pt (cd ∷ cds))
  {i′} (l′ : Location (set l (pileTail (get l))) i′ pt′ cds′) →
  Dec (l ▸ l′)
l ▸? l′ = case get l ▹? get l′ of λ where
  (yes m) → yes (move m)
  (no ¬m) → no λ where (move m) → ¬m m

locationInjective : ∀ {n i pt pt′ cds cds′} {g : Game n} →
  Location g i pt cds → Location g i pt′ cds′ → (pt ≡ pt′) × (cds ≡ cds′)
locationInjective (loc i) (loc .i) = refl , refl

source? : ∀ {n} (g : Game n) i →
  Dec (∃₂ λ cd cds → Location g i (proj₁ (Vec.lookup i (layout g))) (cd ∷ cds))
source? g i
  with proj₂ (Vec.lookup i (layout g)) | inspect (proj₂ ∘ Vec.lookup i) (layout g)
… | [] | [ p ] = no λ where
    (cd , cds , l) → case trans (proj₂ (locationInjective l (loc i))) p of λ ()
… | cd ∷ cds | [ p ] = yes (cd , cds , subst (Location _ _ _) p (loc i))

wonPile? : ∀ pt cds → Dec (WonPile pt cds)
wonPile? cascade [] = yes wonCascade
wonPile? cascade (_ ∷ _) = no λ ()
wonPile? foundation p = yes wonFoundation
wonPile? cell [] = yes wonCell
wonPile? cell (_ ∷ _) = no λ ()

won? : ∀ {n} (g : Game n) → Dec (Won g)
won? = all (uncurry wonPile?) ∘ layout

infixr 6 _þ_
_þ_ : ∀ {pt cds} cd {{pr : PileRule pt cd (listHead cds)}} →
  Pile pt cds → Pile pt (cd ∷ cds)
_ þ p = search ∷ p

infixr 6 _⇒_
_⇒_ : ∀ {n i pt pt′ cd cds cds′} {g : Game n}
  (l : Location g i pt (cd ∷ cds))
  {i′} (l′ : Location (set l (pileTail (get l))) i′ pt′ cds′) →
  {{pr : True (l ▸? l′)}} →
  l ▸ l′
l ⇒ l′ = searchWith (l ▸? l′)
