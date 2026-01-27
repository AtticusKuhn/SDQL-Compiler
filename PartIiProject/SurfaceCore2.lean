import PartIiProject.SurfaceCore

open PartIiProject

/-!
# DeBruijn-indexed Surface Terms (SurfaceCore2)

This module defines a DeBruijn-indexed representation of surface terms,
as an alternative to the PHOAS representation in SurfaceCore.lean.

Key differences from PHOAS:
- Variables are represented by `Mem ty ctx` proofs instead of `rep ty` values
- Context is a `List SurfaceTy` instead of being implicit in the `rep` type
- No higher-order body functions - bodies are just terms in extended contexts
-/

mutual
  /-- A DeBruijn surface term with source location -/
  unsafe inductive STermLoc2 : (ctx : List SurfaceTy) → SurfaceTy → Type where
    | mk : {ctx : List SurfaceTy} → {ty : SurfaceTy} → (loc : SourceLocation) → STerm2 ctx ty → STermLoc2 ctx ty

  /-- DeBruijn-indexed surface term constructors -/
  unsafe inductive STerm2 : (ctx : List SurfaceTy) → SurfaceTy → Type where
    | var   : {ctx : List SurfaceTy} → {ty : SurfaceTy} → Mem ty ctx → STerm2 ctx ty
    | constInt : {ctx : List SurfaceTy} → Int → STerm2 ctx SurfaceTy.int
    | constReal : {ctx : List SurfaceTy} → Float → STerm2 ctx SurfaceTy.real
    | constBool : {ctx : List SurfaceTy} → Bool → STerm2 ctx SurfaceTy.bool
    | constString : {ctx : List SurfaceTy} → String → STerm2 ctx SurfaceTy.string
    | not : {ctx : List SurfaceTy} → STermLoc2 ctx SurfaceTy.bool → STerm2 ctx SurfaceTy.bool
    | ite : {ctx : List SurfaceTy} → {ty : SurfaceTy} → STermLoc2 ctx SurfaceTy.bool → STermLoc2 ctx ty → STermLoc2 ctx ty → STerm2 ctx ty
    | letin : {ctx : List SurfaceTy} → {ty₁ ty₂ : SurfaceTy} → STermLoc2 ctx ty₁ → STermLoc2 (ty₁ :: ctx) ty₂ → STerm2 ctx ty₂
    | add : {ctx : List SurfaceTy} → {ty : SurfaceTy} → (a : SAdd ty) → STermLoc2 ctx ty → STermLoc2 ctx ty → STerm2 ctx ty
    | mul : {ctx : List SurfaceTy} → {sc t1 t2 : SurfaceTy} → (s1 : SScale sc t1) → (s2 : SScale sc t2)
        → STermLoc2 ctx t1 → STermLoc2 ctx t2 → STerm2 ctx (stensor t1 t2)
    | semiringMul : {ctx : List SurfaceTy} → {t : SurfaceTy} → (s1 : SHasMul t)
        → STermLoc2 ctx t → STermLoc2 ctx t → STerm2 ctx t
    | closure : {ctx : List SurfaceTy} → {t : SurfaceTy} → (s1 : SHasClosure t)
        → STermLoc2 ctx t → STerm2 ctx t
    | promote : {ctx : List SurfaceTy} → {fromType toType : SurfaceTy}
        → STermLoc2 ctx fromType → STerm2 ctx toType
    | emptyDict : {ctx : List SurfaceTy} → {domain ran : SurfaceTy} → STerm2 ctx (SurfaceTy.dict domain ran)
    | dictInsert : {ctx : List SurfaceTy} → {dom range : SurfaceTy} → STermLoc2 ctx dom → STermLoc2 ctx range → STermLoc2 ctx (SurfaceTy.dict dom range) → STerm2 ctx (SurfaceTy.dict dom range)
    | lookup : {ctx : List SurfaceTy} → {dom range : SurfaceTy} → (aRange : SAdd range) → STermLoc2 ctx (SurfaceTy.dict dom range) → STermLoc2 ctx dom → STerm2 ctx range
    | sum : {ctx : List SurfaceTy} → {dom range ty : SurfaceTy} → (a : SAdd ty) → STermLoc2 ctx (SurfaceTy.dict dom range) → STermLoc2 (dom :: range :: ctx) ty → STerm2 ctx ty
    | constRecord : {ctx : List SurfaceTy} → {l : Schema}
        → STermFields2 ctx l
        → STerm2 ctx (.record l)
    | projByName : {ctx : List SurfaceTy} → {nm : String} → {t : SurfaceTy} → {σ : Schema}
        → (p : HasField σ nm t)
        → STermLoc2 ctx (.record σ)
        → STerm2 ctx t
    | builtin : {ctx : List SurfaceTy} → {a b : SurfaceTy} → SBuiltin a b → STermLoc2 ctx a → STerm2 ctx b

  /-- Record fields for DeBruijn terms -/
  unsafe inductive STermFields2 : (ctx : List SurfaceTy) → Schema → Type where
    | nil : {ctx : List SurfaceTy} → STermFields2 ctx []
    | cons : {ctx : List SurfaceTy} → {name : String} → {t : SurfaceTy} → {rest : Schema}
        → STermLoc2 ctx t → STermFields2 ctx rest → STermFields2 ctx ((name, t) :: rest)
end

namespace STermLoc2
  /-- Extract the source location from a located term -/
  unsafe def loc {ctx : List SurfaceTy} {ty : SurfaceTy}
      (e : STermLoc2 ctx ty) : SourceLocation :=
    match e with
    | mk l _ => l

  /-- Extract the underlying term from a located term -/
  unsafe def term {ctx : List SurfaceTy} {ty : SurfaceTy}
      (e : STermLoc2 ctx ty) : STerm2 ctx ty :=
    match e with
    | mk _ t => t

  /-- Create a located term with an unknown location -/
  unsafe def withUnknownLoc {ctx : List SurfaceTy} {ty : SurfaceTy}
      (t : STerm2 ctx ty) : STermLoc2 ctx ty :=
    mk SourceLocation.unknown t
end STermLoc2

/-- A program using DeBruijn-indexed terms -/
unsafe structure SProg2 : Type where
  t : SurfaceTy
  ctx : List SurfaceTy
  term : STermLoc2 ctx t
  loadPaths : List String

namespace STerm2

namespace SdqlPretty

def freshNameFrom (candidates : List String) (used : List String) : String :=
  match candidates.find? (fun s => !used.contains s) with
  | some s => s
  | none => s!"x{used.length}"

def freshLetName (used : List String) : String :=
  freshNameFrom ["d", "x", "y", "z", "k", "v", "a", "b", "c", "e"] used

def freshSumKeyName (used : List String) : String :=
  freshNameFrom ["i", "k", "x", "y", "z", "a", "b", "c", "d", "e"] used

def freshSumValName (used : List String) : String :=
  freshNameFrom ["_", "v", "x", "y", "z", "a", "b", "c", "d", "e"] used

def getVarName {ty : SurfaceTy} (names : List String) : {ctx : List SurfaceTy} → Mem ty ctx → String
  | [], m => nomatch m
  | _ :: _, .head _ => names.headD "?"
  | _ :: _, .tail _ m' => getVarName names.tail m'

unsafe abbrev AnyLoc (ctx : List SurfaceTy) : Type :=
  Sigma (fun ty => STermLoc2 ctx ty)

unsafe abbrev AnyTerm (ctx : List SurfaceTy) : Type :=
  Sigma (fun ty => STerm2 ctx ty)

unsafe def packLoc {ctx : List SurfaceTy} {ty : SurfaceTy} (e : STermLoc2 ctx ty) : AnyLoc ctx :=
  Sigma.mk ty e

unsafe def packTerm {ctx : List SurfaceTy} {ty : SurfaceTy} (e : STerm2 ctx ty) : AnyTerm ctx :=
  Sigma.mk ty e

mutual
  unsafe def showNamedFields2 {ctx : List SurfaceTy}
      (names : List String) : {l : Schema} → STermFields2 ctx l → String
    | [], .nil => ""
    | (nm, _) :: _, .cons h t =>
        let hStr := showTermLoc2 names h
        let tStr := showNamedFields2 names t
        let me := s!"{nm} = {hStr}"
        if tStr = "" then me else s!"{me}, {tStr}"
  /-- Render a DeBruijn surface term to sdql-rs-compatible source. -/
  unsafe def showTermLoc2 {ctx : List SurfaceTy} {ty : SurfaceTy}
      (names : List String) (t : STermLoc2 ctx ty) : String :=
    showLoc names (packLoc t)

  unsafe def showLoc {ctx : List SurfaceTy}
      (names : List String) : AnyLoc ctx → String
    | ⟨ty, .mk _ inner⟩ => showTerm names ⟨ty, inner⟩

  unsafe def collectDictEntries? {ctx : List SurfaceTy} :
      AnyLoc ctx → Option (List (AnyLoc ctx × AnyLoc ctx))
    | ⟨ty, t⟩ =>
        match t with
        | .mk _ inner =>
            match packTerm inner with
            | ⟨_, .emptyDict⟩ => some []
            | ⟨_, .dictInsert k v d⟩ =>
                match collectDictEntries? (packLoc d) with
                | some rest => some ((packLoc k, packLoc v) :: rest)
                | none => none
            | _ => none

  unsafe def showDictEntries {ctx : List SurfaceTy}
      (names : List String) : List (AnyLoc ctx × AnyLoc ctx) → String
    | [] => ""
    | [(k, v)] => s!"{showLoc names k} -> {showLoc names v}"
    | (k, v) :: rest => s!"{showLoc names k} -> {showLoc names v}, {showDictEntries names rest}"

  unsafe def unpackRecord2? {ctx : List SurfaceTy} (arg : AnyLoc ctx) : Option (AnyLoc ctx × AnyLoc ctx) :=
    match arg with
    | ⟨_, .mk _ inner⟩ =>
        match packTerm inner with
        | ⟨_, .constRecord fields⟩ =>
            match fields with
            | .cons a (.cons b .nil) => some (packLoc a, packLoc b)
            | _ => none
        | _ => none

  unsafe def unpackRecord3? {ctx : List SurfaceTy} (arg : AnyLoc ctx) :
      Option (AnyLoc ctx × AnyLoc ctx × AnyLoc ctx) :=
    match arg with
    | ⟨_, .mk _ inner⟩ =>
        match packTerm inner with
        | ⟨_, .constRecord fields⟩ =>
            match fields with
            | .cons a (.cons b (.cons c .nil)) => some (packLoc a, packLoc b, packLoc c)
            | _ => none
        | _ => none

  unsafe def showTerm {ctx : List SurfaceTy}
      (names : List String) : AnyTerm ctx → String
    | ⟨_, .var m⟩ => getVarName names m
    | ⟨_, .constInt n⟩ => toString n
    | ⟨_, .constReal r⟩ => toString r
    | ⟨_, .constBool b⟩ => if b then "true" else "false"
    | ⟨_, .constString s⟩ => toString (repr s)
    | ⟨_, .not e⟩ => s!"not {showTermLoc2 names e}"
    | ⟨_, .ite c t f⟩ =>
        s!"if {showTermLoc2 names c} then {showTermLoc2 names t} else {showTermLoc2 names f}"
    | ⟨_, .letin bound body⟩ =>
        let x := freshLetName names
        s!"let {x} = {showTermLoc2 names bound} in {showTermLoc2 (x :: names) body}"
    | ⟨_, .add _ t1 t2⟩ => s!"{showTermLoc2 names t1} + {showTermLoc2 names t2}"
    | ⟨_, .mul _ _ t1 t2⟩ => s!"{showTermLoc2 names t1} * {showTermLoc2 names t2}"
    | ⟨_, .semiringMul _ t1 t2⟩ => s!"{showTermLoc2 names t1} *s {showTermLoc2 names t2}"
    | ⟨_, .closure _ e⟩ => s!"closure({showTermLoc2 names e})"
    | ⟨toType, @STerm2.promote _ _ _ e⟩ =>
        s!"promote[{SurfaceTy.sdqlToString toType}]({showTermLoc2 names e})"
    | ⟨_, .emptyDict⟩ => "{}"
    | ⟨_, .dictInsert k v d⟩ =>
        match collectDictEntries? (packLoc (STermLoc2.withUnknownLoc (.dictInsert k v d))) with
        | some entries =>
            let content := showDictEntries names entries
            "{ " ++ content ++ " }"
        | none =>
            s!"<unsupported_dict_insert {showTermLoc2 names k} {showTermLoc2 names v} {showTermLoc2 names d}>"
    | ⟨_, .lookup _ d k⟩ => s!"{showTermLoc2 names d}({showTermLoc2 names k})"
    | ⟨_, .sum _ d body⟩ =>
        let k := freshSumKeyName names
        let v := freshSumValName (k :: names)
        s!"sum(<{k},{v}> <- {showTermLoc2 names d}) {showTermLoc2 (k :: v :: names) body}"
    | ⟨_, .constRecord fields⟩ => "<" ++ showNamedFields2 names fields ++ ">"
    | ⟨_, .projByName (nm := nm) _ record⟩ => s!"{showTermLoc2 names record}.{nm}"
    | ⟨_, .builtin b arg⟩ =>
        let argAny := packLoc arg
        match b with
        | .Range => s!"range({showLoc names argAny})"
        | .Dom => s!"dom({showLoc names argAny})"
        | .Size => s!"size({showLoc names argAny})"
        | .Year => s!"year({showLoc names argAny})"
        | .DateLit yyyymmdd => s!"date({yyyymmdd})"
        | .StrEndsWith =>
            match unpackRecord2? argAny with
            | some (a, b) => s!"endsWith({showLoc names a}, {showLoc names b})"
            | none => s!"StrEndsWith({showLoc names argAny})"
        | .StrStartsWith =>
            match unpackRecord2? argAny with
            | some (a, b) => s!"StrStartsWith({showLoc names a}, {showLoc names b})"
            | none => s!"StrStartsWith({showLoc names argAny})"
        | .StrContains =>
            match unpackRecord2? argAny with
            | some (a, b) => s!"StrContains({showLoc names a}, {showLoc names b})"
            | none => s!"StrContains({showLoc names argAny})"
        | .FirstIndex =>
            match unpackRecord2? argAny with
            | some (a, b) => s!"FirstIndex({showLoc names a}, {showLoc names b})"
            | none => s!"FirstIndex({showLoc names argAny})"
        | .LastIndex =>
            match unpackRecord2? argAny with
            | some (a, b) => s!"LastIndex({showLoc names a}, {showLoc names b})"
            | none => s!"LastIndex({showLoc names argAny})"
        | .SubString =>
            match unpackRecord3? argAny with
            | some (s, start, stop) =>
                s!"SubString({showLoc names s}, {showLoc names start}, {showLoc names stop})"
            | none => s!"SubString({showLoc names argAny})"
        | .Concat _ _ =>
            match unpackRecord2? argAny with
            | some (a, b) => s!"concat({showLoc names a}, {showLoc names b})"
            | none => s!"concat({showLoc names argAny})"
        | .And =>
            match unpackRecord2? argAny with
            | some (a, b) => s!"{showLoc names a} && {showLoc names b}"
            | none => s!"({showLoc names argAny})"
        | .Or =>
            match unpackRecord2? argAny with
            | some (a, b) => s!"{showLoc names a} || {showLoc names b}"
            | none => s!"({showLoc names argAny})"
        | .Eq =>
            match unpackRecord2? argAny with
            | some (a, b) => s!"{showLoc names a} == {showLoc names b}"
            | none => s!"({showLoc names argAny})"
        | .Leq =>
            match unpackRecord2? argAny with
            | some (a, b) => s!"{showLoc names a} <= {showLoc names b}"
            | none => s!"({showLoc names argAny})"
        | .Lt =>
            match unpackRecord2? argAny with
            | some (a, b) => s!"{showLoc names a} < {showLoc names b}"
            | none => s!"({showLoc names argAny})"
        | .Sub =>
            match unpackRecord2? argAny with
            | some (a, b) => s!"{showLoc names a} - {showLoc names b}"
            | none => s!"({showLoc names argAny})"
        | .Div =>
            match unpackRecord2? argAny with
            | some (a, b) => s!"{showLoc names a} / {showLoc names b}"
            | none => s!"({showLoc names argAny})"
end

end SdqlPretty

end STerm2

namespace SProg2

open STerm2.SdqlPretty

def loadNameCandidates : List String :=
  ["t", "u", "v", "w", "x", "y", "z"]

def mkLoadNames (tys : List SurfaceTy) : List String :=
  let rec go (tys : List SurfaceTy) (used : List String) : List String :=
    match tys with
    | [] => []
    | _ :: rest =>
        let nm := freshNameFrom loadNameCandidates used
        nm :: go rest (nm :: used)
  go tys []

unsafe def showTopLetChain {ctx : List SurfaceTy} {ty : SurfaceTy}
    (names : List String) (e : STermLoc2 ctx ty) : String :=
  match packTerm e.term with
  | ⟨_, .letin bound body⟩ =>
      let x := freshLetName names
      s!"let {x} = {showTermLoc2 names bound}\n{showTopLetChain (x :: names) body}"
  | _ => showTermLoc2 names e

unsafe def toSdqlString (sp : SProg2) : String :=
  let ctxNames := mkLoadNames sp.ctx
  let core := showTopLetChain ctxNames sp.term
  let triples : List (String × SurfaceTy × String) :=
    (ctxNames.zip sp.ctx).zip sp.loadPaths |>.map (fun ((nm, ty), p) => (nm, ty, p))
  triples.reverse.foldl
    (fun acc (nm, ty, path) =>
      s!"let {nm} = load[{SurfaceTy.sdqlToString ty}]({toString (repr path)})\n{acc}")
    core

end SProg2

unsafe instance : ToString SProg2 :=
  { toString := SProg2.toSdqlString }
