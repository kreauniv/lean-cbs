inductive Resource where
  | file : String → Resource  -- identified by path
  deriving DecidableEq, Repr

inductive Authority where
  | read
  | write
  | delete
  deriving DecidableEq, Repr

/-
unique identifier per capability token
-/
abbrev CapId := Nat

structure Cap where
  private mk ::
  resource : Resource
  authority : Authority
  identity : CapId
  deriving Repr

inductive CapCmd : Type → Type where
  | read   : Cap → CapCmd String
  | write  : Cap → String → CapCmd Unit
  | delete : Cap → CapCmd Unit

inductive CapM : Type → Type _ where
  | pure : α → CapM α
  | cons : CapCmd β → (β → CapM α) → CapM α

def CapM.flatMap {α β : Type} (f : α → CapM β) : CapM α → CapM β
  | .pure a => f a
  | .cons cmd k => .cons cmd (fun b => (k b).flatMap f)

instance : Monad CapM where
  pure := CapM.pure
  bind x f := CapM.flatMap f x

def CapM.read (c : Cap) : CapM String := .cons (CapCmd.read c) .pure
def CapM.write (c : Cap) (s : String) : CapM Unit := .cons (CapCmd.write c s) .pure
def CapM.delete (c : Cap) : CapM Unit := .cons (CapCmd.delete c) .pure

/-
Each agent has a list of held capabilities
-/
structure CapEnv where
  nextId : CapId -- every issued cap gets a new Id
  wallet : List Cap -- a capability is valid IFF it is present here. Revoking means removing from here.
  revoked : List CapId -- ids that have been invalidated since issuance


/-
Held Predicate for checking for membership
-/
def CapEnv.valid (env : CapEnv) (c : Cap) : Prop :=
  c ∈ env.wallet

def CapEnv.revoke (env : CapEnv) (id : CapId): CapEnv :=
  { nextId := env.nextId,
    wallet := env.wallet.filter (fun c => c.identity ≠ id)
    revoked := env.revoked ++ [id]
  }

inductive SafeProg : {α : Type} → CapEnv → CapM α → Prop where
  | pureSafe (env : CapEnv) (a : α) : SafeProg env (CapM.pure a)
  | readSafe (env : CapEnv) (c : Cap) (k : String → CapM α)
      (hv : env.valid c)
      (ha : c.authority = .read) :
      SafeProg env (CapM.read c)
  | writeSafe (env : CapEnv) (c : Cap) (s : String) (k : Unit → CapM α)
      (hv : env.valid c)
      (ha : c.authority = .write):
      SafeProg env (CapM.write c s)
  | deleteSafe (env : CapEnv) (c : Cap) (k : Unit → CapM α)
      (hv : env.valid c)
      (ha : c.authority = .delete) :
      SafeProg env (CapM.delete c)
  | flatMapSafe (env : CapEnv) (x : CapM α) (f : α → CapM β)
      (h1 : SafeProg env x)
      (h2 : ∀ a, SafeProg env (f a)) :
      SafeProg env (CapM.flatMap f x)
