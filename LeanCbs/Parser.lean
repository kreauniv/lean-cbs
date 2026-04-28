import LeanCbs.Core
import Lean.Data.Json

open Lean (Json)

/-
  DSL AST : Intermediate form between raw JSON and a verified CapM program.
-/
inductive DslNode where
  | read   (capName : String)
  | write  (capName : String) (contents : String)
  | delete (capName : String)
  | seq    (first rest : DslNode)
  deriving Repr

/-
  Parser Errors
-/
inductive ParseError where
  | malformed         (msg  : String)
  | unknownKind       (kind : String)
  | missingField      (field : String)
  | unknownCap        (name : String)
  | invalidCap        (name : String)
  | authorityMismatch (name : String) (expected : Authority)
  deriving Repr

instance : Inhabited ParseError := ⟨.malformed ""⟩

/-
  ResolveMap
-/

abbrev ResolveMap := List (String × Cap)

def ResolveMap.lookup (m : ResolveMap) (name : String) : Option Cap :=
  m.find? (fun p => p.1 == name) |>.map Prod.snd

structure VerifiedProg (env : CapEnv) : Type 1 where
  α     : Type
  prog  : CapM α
  hSafe : SafeProg env prog

/-
  JSON -> DSL Schema Validation
-/

private def getStrField (j : Json) (field : String) : Except ParseError String :=
  match j.getObjVal? field with
  | .error _    => .error (.missingField field)
  | .ok (.str s) => .ok s
  | .ok _       => .error (.malformed s!"field '{field}' is not a string")

private def getObjField (j : Json) (field : String) : Except ParseError Json :=
  match j.getObjVal? field with
  | .error _ => .error (.missingField field)
  | .ok v    => .ok v

partial def parseDsl (j : Json) : Except ParseError DslNode := do
  let kind ← getStrField j "kind"
  match kind with
  | "read" =>
      let cap ← getStrField j "capability"
      return .read cap
  | "write" =>
      let cap      ← getStrField j "capability"
      let contents ← getStrField j "contents"
      return .write cap contents
  | "delete" =>
      let cap ← getStrField j "capability"
      return .delete cap
  | "seq" =>
      let firstJ ← getObjField j "first"
      let restJ  ← getObjField j "rest"
      let first ← parseDsl firstJ
      let rest  ← parseDsl restJ
      return .seq first rest
  | other => .error (.unknownKind other)

/-
  DslNode -> Verified Prog

   For each leaf node:
     - look up the capability name in the resolve map
     - decide `env.valid c` (Cap has DecidableEq)
     - decide `c.authority = <expected>` (Authority has DecidableEq)
     - emit the corresponding SafeProg constructor

   For `seq`: recurse on both subnodes andcombine with `flatMapSafe`.
-/

def verify (env : CapEnv) (m : ResolveMap) :
    DslNode → Except ParseError (VerifiedProg env)
  | .read capName =>
      match m.lookup capName with
      | none => .error (.unknownCap capName)
      | some c =>
          if h : env.valid c then
            if ha : c.authority = .read then
              .ok ⟨String, CapM.read c, SafeProg.readSafe env c h ha⟩
            else
              .error (.authorityMismatch capName .read)
          else
            .error (.invalidCap capName)
  | .write capName contents =>
      match m.lookup capName with
      | none => .error (.unknownCap capName)
      | some c =>
          if h : env.valid c then
            if ha : c.authority = .write then
              .ok ⟨Unit, CapM.write c contents,
                   SafeProg.writeSafe env c contents h ha⟩
            else
              .error (.authorityMismatch capName .write)
          else
            .error (.invalidCap capName)
  | .delete capName =>
      match m.lookup capName with
      | none => .error (.unknownCap capName)
      | some c =>
          if h : env.valid c then
            if ha : c.authority = .delete then
              .ok ⟨Unit, CapM.delete c, SafeProg.deleteSafe env c h ha⟩
            else
              .error (.authorityMismatch capName .delete)
          else
            .error (.invalidCap capName)
  | .seq first rest =>
      match verify env m first with
      | .error e => .error e
      | .ok va =>
          match verify env m rest with
          | .error e => .error e
          | .ok vb =>
              .ok ⟨vb.α,
                   va.prog.flatMap (fun _ => vb.prog),
                   SafeProg.flatMapSafe env va.prog va.hSafe
                     (fun _ => vb.hSafe)⟩

/- ===========================================================
   Top-level entry point
   =========================================================== -/

def parseAndVerify (env : CapEnv) (m : ResolveMap) (j : Json) :
    Except ParseError (VerifiedProg env) :=
  match parseDsl j with
  | .error e => .error e
  | .ok node => verify env m node
