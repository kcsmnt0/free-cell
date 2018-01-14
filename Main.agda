module Main where

open import Coinduction using (♯_; ♭)
open import Data.Bool using (Bool; true; false; if_then_else_)
import Data.BoundedVec.Inefficient as BoundedVec
open import Data.Char using (Char)
open import Data.Colist as Colist using (Colist; []; _∷_)
open import Data.Digit using (digitChars)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe as Maybe using (Maybe; just; nothing; decToMaybe)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.String as String using (String; Costring; _==_; _++_)
open import Data.Unit as ⊤ using (⊤)
open import Data.Vec as Vec using (Vec; _∷_; []; allFin; allPairs)
open import Data.Vec.All using (All; _∷_; [])
open import Function
open import IO
open import Relation.Nullary using (Dec; yes; no)

open import Display
open import Game
open import Validation

codrop : ∀ {a} {A : Set a} → ℕ → Colist A → Colist A
codrop n [] = []
codrop zero xs = xs
codrop (suc n) (x ∷ xs) = codrop n (♭ xs)

Scan : ∀ {a b c} → Set a → Set b → Set c → Set _
Scan A B C = Colist A → B → Maybe (ℕ × B × C)

scan : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
  Scan A B C → Colist A → B → Colist C
scan f xs y with f xs y
… | nothing = []
… | just (n , y′ , z) = z ∷ ♯ scan f (codrop n xs) y′

takeString : ℕ → Costring → String
takeString n = String.fromList ∘ BoundedVec.toList ∘ Colist.take n

menu : ∀ {a b} {A : Set a} {B : Set b} →
  B → List (String × (A → Maybe (A × B))) →
  Scan Char A B
menu d [] xs y = just (1 , y , d)
menu d ((s , f) ∷ fs) xs y =
  let
    s′ = String.toList s List.∷ʳ '\n'
    len = List.length s′
  in
    if takeString len xs == String.fromList s′ then
      Maybe.map (_,_ len) (f y)
    else
      menu d fs xs y

tryMove : ∀ {n} (g : Game n) → Fin n → Fin n → Maybe (Game n)
tryMove g i j = case source? g i of λ where
  (yes (_ , _ , l)) → Maybe.map makeLocMove (decToMaybe (l ▸? loc j))
  (no _) → nothing

play : Scan Char (Game 16) (IO ⊤)
play = menu (return _) (List.map act indices List.++ win ∷ quit ∷ [])
  where
    win = "win" , λ g → case won? g of λ where
      (yes w) → just (g , putStrLn "yes you did!")
      (no _) → just (g , putStrLn "no you didn't.")

    quit = "quit" , const nothing

    act : _ → _
    act ((x , y) , (i , j)) =
      x ++ " " ++ y , λ g → case tryMove g i j of λ where
        (just g′) → just (g′ , putStrLn (displayGame g′))
        nothing → just (g , (♯ putStrLn "bad move" >> ♯ putStrLn (displayGame g)))

    digits = Vec.map (String.fromList ∘ List.[_]) digitChars

    indices =
      Vec.toList
        (Vec.zip
          (allPairs digits digits)
          (allPairs (allFin _) (allFin _)))

-- the Agda standard library doesn't have a random number API
-- so this is an artisinal hand-chosen initial deal
initial = deal
  ( []
  ∷ []
  ∷ []
  ∷ []
  ∷ [] )

  ( []
  ∷ []
  ∷ []
  ∷ []
  ∷ [] )

  (   five of ♥ is unmoved
    þ three of ♥ is unmoved
    þ two of ♠ is unmoved
    þ eight of ♣ is unmoved
    þ queen of ♥ is unmoved
    þ six of ♠ is unmoved
    þ four of ♣ is unmoved
    þ []

  ∷   three of ♠ is unmoved
    þ ten of ♥ is unmoved
    þ nine of ♢ is unmoved
    þ nine of ♠ is unmoved
    þ eight of ♢ is unmoved
    þ king of ♠ is unmoved
    þ seven of ♢ is unmoved
    þ []

  ∷   four of ♢ is unmoved
    þ ace of ♢ is unmoved
    þ king of ♣ is unmoved
    þ nine of ♥ is unmoved
    þ jack of ♢ is unmoved
    þ eight of ♠ is unmoved
    þ four of ♠ is unmoved
    þ []

  ∷   seven of ♣ is unmoved
    þ three of ♣ is unmoved
    þ ten of ♢ is unmoved
    þ seven of ♠ is unmoved
    þ ace of ♥ is unmoved
    þ ace of ♣ is unmoved
    þ three of ♢ is unmoved
    þ []

  ∷   king of ♢ is unmoved
    þ ace of ♠ is unmoved
    þ six of ♣ is unmoved
    þ jack of ♠ is unmoved
    þ six of ♥ is unmoved
    þ king of ♥ is unmoved
    þ []

  ∷   ten of ♣ is unmoved
    þ jack of ♣ is unmoved
    þ five of ♢ is unmoved
    þ jack of ♥ is unmoved
    þ nine of ♣ is unmoved
    þ eight of ♥ is unmoved
    þ []

  ∷   ten of ♠ is unmoved
    þ queen of ♢ is unmoved
    þ five of ♣ is unmoved
    þ five of ♠ is unmoved
    þ six of ♢ is unmoved
    þ queen of ♠ is unmoved
    þ []

  ∷   two of ♣ is unmoved
    þ queen of ♣ is unmoved
    þ four of ♥ is unmoved
    þ two of ♢ is unmoved
    þ two of ♥ is unmoved
    þ seven of ♥ is unmoved
    þ []

  ∷ [] )

main = run do
  input ← ♯ getContents
  ♯ do
    ♯ putStrLn (displayGame initial)
    ♯ sequence′ (scan play input initial)
