inductive Ty : Type where
  | bool : Ty
  | string : Ty
  | int :  Ty
  deriving Inhabited


def Ty.denote : Ty → Type
  | Ty.bool => Bool
  | Ty.string => String
  | Ty.int => Int

inductive SM : Ty → Ty →  Type where
  | boolSM : SM Ty.bool Ty.bool
  | intSm : SM Ty.int Ty.int

class SemiModule (s : Type) (x : Type) :  Type where
  add : x → x → x
  mutliply : s → x → x

instance SMB : SemiModule Bool Bool where
  add := Bool.xor
  mutliply := Bool.and

instance SMI : SemiModule Int Int where
  add := Int.add
  mutliply := Int.mul

def SM.denote {a b : Ty} (sm : SM a b)  : SemiModule (Ty.denote a) (Ty.denote b) :=
  match sm with
    | SM.boolSM => SMB
    | SM.intSm => SMI



inductive Term' (rep : Ty → Type) : Ty → Type
  | var   : {ty : Ty} → rep ty → Term' rep ty
  | constInt : Int → Term' rep  Ty.int
  | constBool : Bool → Term' rep Ty.bool
  | constString : String → Term' rep Ty.string
  | add : {ty sc : Ty} → (_s : SM sc ty) → Term' rep ty → Term' rep ty → Term' rep ty

def Term'.denote {ty : Ty} : Term' Ty.denote ty → ty.denote
  | Term'.var v => v
  | Term'.constInt n => n
  | Term'.constBool b => b
  | Term'.constString s => s
  | Term'.add sm t1 t2 =>
    let sm' := SM.denote sm
    sm'.add (denote t1) (denote t2)

-- instance basic : SemiModule String String where
--   add := fun _ _ => ""
--   mutliply := fun _ _ => ""

-- def Term'.show1 {ty : Ty} : Term' (fun _ => String) (fun _ => basic) ty → String
--   | Term'.var v => v
--   | Term'.constInt n => toString n
--   | Term'.constBool b => toString b
--   | Term'.constString s => s
--   | Term'.add sm t1 t2 => s!"{t1.show1} + {t2.show1}"

def Term'.show {ty : Ty} : Term' (fun _ => String) ty → String
  | .var v           => v
  | .constInt n      => toString n
  | .constBool b     => toString b
  | .constString s   => s
  | .add sn t1 t2     => s!"{t1.show} + {t2.show}"  -- note: ignore the SM evidence


-- def Term'.show {ty : Ty} : Term' (fun _ => String) (sm := fun a b => String) (fun _ => " ") ty → String
--   | Term'.var v => v
--   | Term'.constInt n => toString n
--   | Term'.constBool b => toString b
--   | Term'.constString s => s
--   | Term'.add sm t1 t2 => s!"{t1.show} + {t2.show}"


def Term (ty : Ty) := {rep : Ty → Type} → Term' rep ty



def test : Term Ty.int :=
  Term'.add (SM.intSm) (Term'.constInt 3) (Term'.constInt 5)

def test2 : Term Ty.bool :=
  Term'.add (SM.boolSM) (Term'.constBool true) (Term'.constBool false)

def Term.show {ty : Ty} (t : Term ty) : String :=
  Term'.show (t)
set_option pp.explicit true

#eval Term'.denote test
#eval Term'.denote test2

#eval Term.show test
#eval Term.show test2
