def doble (n: Nat) : Nat := 2*n

#eval doble 3
#check doble
#check (doble)

def maximum (n : Nat) (k : Nat) : Nat :=
  if n < k then
    k
  else n

#eval maximum 3 4
#check (maximum)

#check maximum 3

def joinStringsWith (fst snd trd: String): String := String.append snd (String.append fst trd)

#eval joinStringsWith ": " "Hola" "Hpta"

structure Point where
  x : Float
  y : Float
deriving Repr

def origin : Point := { x := 0.0, y := 0.0 }
#eval origin
#eval origin.x

def addPoints (p1 p2 : Point) : Point :=
  { x := p1.x + p2.x, y := p1.y + p2.y }

def zeroX (p : Point) : Point :=
  { p with x := 0 }

structure Point2 where
  point ::
  x : Float
  y : Float
deriving Repr

#eval Point2.point 1 2

def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => false

def pred (n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ k => k

def even (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (even k)

#eval even 1000

def div (n : Nat) (k : Nat) : Nat :=
  if n < k then
    0
  else Nat.succ (div (n - k) k)

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

def natOrigin : PPoint Nat :=
  { x := Nat.zero, y := Nat.zero }

/-Buena sintaxis para reemplazar-/
def replaceX (α : Type) (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }

#check replaceX Nat natOrigin

inductive Sign where
  | pos
  | neg

/-Qué jodida señora estructura de método-/
def posOrNegThree (s : Sign) : match s with | Sign.pos => Nat | Sign.neg => Int :=
  match s with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)

def primesUnder10 : List Nat := [2, 3, 5, 7]

def length (α : Type) (xs : List α) : Nat :=
  match xs with
  | List.nil => Nat.zero
  | List.cons y ys => Nat.succ (length α ys)

def length2 (α : Type) (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => Nat.succ (length α ys)

#check List.length (α := Int)

/-
inductive Option (α : Type) : Type where
  | none : Option α
  | some (val : α) : Option α

def List.head? {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | y :: _ => some y

structure Prod (α : Type) (β : Type) : Type where
  fst : α
  snd : β
-/

def PetName : Type := String ⊕ String

def animals : List PetName :=
  [Sum.inl "Spot", Sum.inr "Tiger", Sum.inl "Fifi", Sum.inl "Rex", Sum.inr "Floof"]

def howManyDogs (pets : List PetName) : Nat :=
  match pets with
  | [] => 0
  | Sum.inl _ :: morePets => howManyDogs morePets + 1
  | Sum.inr _ :: morePets => howManyDogs morePets

#eval howManyDogs animals

def lastEntry? (α : Type) (lista : List α) : Option α :=
  match lista with
  | h :: [] => h
  | _ :: t => lastEntry? α t
  | [] => none

#eval lastEntry? Int [1, 2, 3, 4]
#eval lastEntry? Int []

def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=
  match xs with
  | [] => none
  | x :: s => match predicate x with
              | true => some x
              | false => List.findFirst? s predicate

#check List.findFirst? [1, 2, 3, 4] (fun x => x>5)
#eval List.findFirst? [1, 2, 3, 4] (fun x => x>5)
#eval List.findFirst? [1, 2, 3, 4] (fun x => x<5)

def Prod.swap {α β : Type} (pair : α × β) : β × α :=
  {fst := pair.snd, snd := pair.fst}
def fives : String × Int := ("five", 5)
#eval Prod.swap fives


#eval List.length [12,3, 4]
#check Sort 0
#check Sort
#check Type 1
def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  match p: (List.length xs < List.length ys) with
  | true => []
  | false => []

def zip2 {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  if (List.length xs < List.length ys) then
    []
  else
    []


#eval Eq.subst (motive := fun x => x < 5)
