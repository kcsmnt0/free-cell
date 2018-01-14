module Game where

open import Data.Fin using (Fin; zero; suc; inject₁)
open import Data.List as List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; uncurry)
open import Data.Vec as Vec using (Vec; []; _∷_; _[_]≔_)
open import Data.Vec.All as All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Function

listHead : {A : Set} → List A → Maybe A
listHead [] = nothing
listHead (x ∷ _) = just x

update : ∀ {A : Set} {P : A → Set} {n x} {xs : Vec A n}
  i → P x → All P xs → All P (xs [ i ]≔ x)
update zero p (_ ∷ ps) = p ∷ ps
update (suc i) p (q ∷ ps) = q ∷ update i p ps

infixr 5 _++A_
_++A_ : ∀ {A : Set} {P : A → Set} {m n} {xs : Vec A m} {ys : Vec A n} →
  All P xs → All P ys → All P (xs Vec.++ ys)
[] ++A qs = qs
(p ∷ ps) ++A qs = p ∷ ps ++A qs

Rank = Fin 13

data Color : Set where
  red black : Color

otherColor : Color → Color
otherColor red = black
otherColor black = red

data State : Set where
  unmoved moved : State

data Suit : Color → Set where
  ♥ ♢ : Suit red
  ♠ ♣ : Suit black

pattern ace   = zero
pattern two   = suc ace
pattern three = suc two
pattern four  = suc three
pattern five  = suc four
pattern six   = suc five
pattern seven = suc six
pattern eight = suc seven
pattern nine  = suc eight
pattern ten   = suc nine
pattern jack  = suc ten
pattern queen = suc jack
pattern king  = suc queen
pattern king+ x = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc x))))))))))))

infix 7 _of_is_
record Card : Set where
  constructor _of_is_
  field
    {color} : Color
    rank : Rank
    suit : Suit color
    state : State

open Card public

touch : Card → Card
touch (r of s is _) = r of s is moved

ConsRule = Card → Maybe Card → Set

infixr 6 _▹Cascade_
data _▹Cascade_ : ConsRule where
  instance
    unmovedStart : ∀ {c r} {s : Suit c} →
      r of s is unmoved ▹Cascade nothing

    unmovedCons : ∀ {c c′ r r′} {s : Suit c} {s′ : Suit c′} →
      r of s is unmoved ▹Cascade just (r′ of s′ is unmoved)

    movedStart : ∀ {c} {s : Suit c} →
      king of s is moved ▹Cascade nothing

    movedCons : ∀ {c r st} {s : Suit c} {s′ : Suit (otherColor c)} →
      inject₁ r of s is moved ▹Cascade just (suc r of s′ is st)

infixr 6 _▹Foundation_
data _▹Foundation_ : ConsRule where
  instance
    start : ∀ {c st} {s : Suit c} →
      ace of s is st ▹Foundation nothing

    cons : ∀ {c r st st′} {s : Suit c} →
      suc r of s is st ▹Foundation just (inject₁ r of s is st′)

infixr 6 _▹Cell_
data _▹Cell_ : ConsRule where
  instance
    start : ∀ {cd} → cd ▹Cell nothing

data PileType : Set where cascade foundation cell : PileType

PileRule : PileType → ConsRule
PileRule cascade = _▹Cascade_
PileRule foundation = _▹Foundation_
PileRule cell = _▹Cell_

data Pile (pt : PileType) : List Card → Set where
  [] : Pile pt []
  _∷_ : ∀ {cd cds} →
    PileRule pt cd (listHead cds) → Pile pt cds → Pile pt (cd ∷ cds)

uncons : ∀ {pt cd cds} → Pile pt (cd ∷ cds) →
  PileRule pt cd (listHead cds) × Pile pt cds
uncons (pr ∷ p) = pr , p

pileHead : ∀ {pt cd cds} → Pile pt (cd ∷ cds) → PileRule pt cd (listHead cds)
pileHead = proj₁ ∘ uncons

pileTail : ∀ {pt cd cds} → Pile pt (cd ∷ cds) → Pile pt cds
pileTail = proj₂ ∘ uncons

infixr 6 _▹_
data _▹_ {pt pt′ cds′} : ∀ {cds} → Pile pt cds → Pile pt′ cds′ → Set where
  move : ∀ {cd cds}
    {p : Pile pt (cd ∷ cds)} {p′ : Pile pt′ cds′} →
    PileRule pt′ (touch cd) (listHead cds′) → p ▹ p′

makeMove : ∀ {pt pt′ cd cds cds′} {p : Pile pt (cd ∷ cds)} {p′ : Pile pt′ cds′} →
  p ▹ p′ → Pile pt cds × Pile pt′ (touch cd ∷ cds′)
makeMove (move {p = _ ∷ p} {p′} pr) = p , pr ∷ p′

Layout = Vec (PileType × List Card)

record Game n : Set where
  constructor game
  field
    {layout} : Layout n
    piles : All (uncurry Pile) layout

  data Location : Fin n → PileType → List Card → Set where
    loc : ∀ i → uncurry (Location i) (Vec.lookup i layout)

open Game public

get : ∀ {n i pt cds} {g : Game n} → Location g i pt cds → Pile pt cds
get {g = g} (loc i) = All.lookup i (piles g)

set : ∀ {n i pt cds cds′} {g : Game n} →
  Location g i pt cds → Pile pt cds′ → Game n
set {g = g} (loc i) p = record { piles = update i p (piles g) }

infixr 6 _▸_
data _▸_ {n i pt pt′ cd cds cds′} {g : Game n}
    (l : Location g i pt (cd ∷ cds)) {i′}
    (l′ : Location (set l (pileTail (get l))) i′ pt′ cds′) :
    Set where
  move : get l ▹ get l′ → l ▸ l′

makeLocMove : ∀ {n i pt pt′ cd cds cds′} {g : Game n}
  {l : Location g i pt (cd ∷ cds)} {i′} {l′ : Location (set l (pileTail (get l))) i′ pt′ cds′} →
  l ▸ l′ → Game n
makeLocMove {l′ = l′} (move m) = set l′ (proj₂ (makeMove m))

-- the game is won when only foundations have cards
-- (assuming the integrity of all piles)
data WonPile : PileType → List Card → Set where
  instance
    wonCell : WonPile cell []
    wonCascade : WonPile cascade []
    wonFoundation : ∀ {cds} → WonPile foundation cds

WonLayout : ∀ {n} (layout : Vec _ n) → Set
WonLayout = All (uncurry WonPile)

Won : ∀ {n} → Game n → Set
Won = WonLayout ∘ layout

data Session {n} (g : Game n) : Set where
  [] : Session g
  _∷_ : ∀ {pt i pt′ cd cds cds′}
    {l : Location g i pt (cd ∷ cds)} {i′} {l′ : Location (set l (pileTail (get l))) i′ pt′ cds′} →
    (m : l ▸ l′) → Session (makeLocMove m) → Session g

sessionEnd : ∀ {n} {g : Game n} → Session g → Game n
sessionEnd {g = g} [] = g
sessionEnd (_ ∷ s) = sessionEnd s

deal : ∀
  {l m n}
  {cellContents : Vec _ l}
  {foundationContents : Vec _ m}
  {cascadeContents : Vec _ n} →
  All (uncurry Pile) (Vec.map (_,_ cell) cellContents) →
  All (uncurry Pile) (Vec.map (_,_ foundation) foundationContents) →
  All (uncurry Pile) (Vec.map (_,_ cascade) cascadeContents) →
  Game _
deal cellPiles foundationPiles cascadePiles =
  record { piles = cellPiles ++A foundationPiles ++A cascadePiles }
