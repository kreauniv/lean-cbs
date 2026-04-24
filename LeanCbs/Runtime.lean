import LeanCbs.Core
open IO FS System

/- ===========================================================
   Cap minting API
   =========================================================== -/

def CapEnv.revoke (env : CapEnv) (id : CapId): CapEnv :=
  { nextId := env.nextId,
    wallet := env.wallet.filter (fun c => c.identity ≠ id)
    revoked := env.revoked ++ [id]
  }

/- ===========================================================
   Pure cap-layer checks
   =========================================================== -/
/-
Looks at one command and decides whether that command is allowed under
the current capability environment.
-/
def CapCmd.check (env : CapEnv) : {β : Type} → CapCmd β → Except CapError Unit
  | _, .read c =>
      if !env.isValid c then .error (.invalidCap c.identity)
      else if c.authority != .read then .error .wrongAuthority
      else .ok ()
  | _, .write c _ =>
      if !env.isValid c then .error (.invalidCap c.identity)
      else if c.authority != .write then .error .wrongAuthority
      else .ok ()
  | _, .delete c =>
      if !env.isValid c then .error (.invalidCap c.identity)
      else if c.authority != .delete then .error .wrongAuthority
      else .ok ()

/-
Head-of-program cap check: inspects only the outermost command of `prog`.
-/
-- def CapM.checkHead (env : CapEnv) : {α : Type} → CapM α → Except CapError Unit
--   | _, .pure _    => .ok ()
--   | _, .cons cmd _ => CapCmd.check env cmd

/- ===========================================================
   Soundness theorems
   =========================================================== -/

/-
Soundness of the cap layer — pure, provable, no `IO` anywhere.

"If a program is safe under `env`, then the cap-layer pre-pass accepts
its head command." Because `CapM.run` now guards every step on exactly
`CapCmd.check`, the `.error` branch of the interpreter is unreachable
on a `SafeProg` — the `CapError` path has been closed off at the type
level, not at runtime.
-/
-- theorem SafeProg.checkHead_ok {α : Type} {env : CapEnv} {prog : CapM α}
--     (h : SafeProg env prog) : CapM.checkHead env prog = .ok () := by
--   induction h with
--   | pureSafe _ _ => rfl
--   | readSafe _ c hv ha =>
--       simp [CapM.checkHead, CapM.read, CapCmd.check,
--             CapEnv.isValid_of_valid hv, ha]
--   | writeSafe _ c s hv ha =>
--       simp [CapM.checkHead, CapM.write, CapCmd.check,
--             CapEnv.isValid_of_valid hv, ha]
--   | deleteSafe _ c hv ha =>
--       simp [CapM.checkHead, CapM.delete, CapCmd.check,
--             CapEnv.isValid_of_valid hv, ha]
--   | flatMapSafe _ x _ _ ih1 ih2 =>
--       cases x with
--       | pure a =>
--           -- (pure a).flatMap f = f a
--           exact ih2 a
--       | cons cmd k =>
--           -- (cons cmd k).flatMap f = cons cmd (...), same head cmd as x
--           exact ih1

/-
Full-trace soundness. `checkHead_ok` only covers the outermost command;
to claim the interpreter never raises a `CapError` on *any* step we need
an invariant that talks about the whole tree of reachable continuations.

`AllSafe env prog` says: every command anywhere in `prog` (head, and all
continuations after every possible runtime input) passes `CapCmd.check`.
The `cons` case carries `∀ b, AllSafe env (k b)` — universal over the
continuation's input, exactly because we cannot inspect runtime values
at proof time.
-/
inductive AllSafe (env : CapEnv) : {α : Type} → CapM α → Prop where
  | pure {α : Type} (a : α) : AllSafe env (CapM.pure a)
  | cons {α β : Type} (cmd : CapCmd β) (k : β → CapM α)
      (hcheck : CapCmd.check env cmd = .ok ())
      (hk : ∀ b, AllSafe env (k b)) :
      AllSafe env (CapM.cons cmd k)

/-
`AllSafe` is preserved by `flatMap`: if every reachable command in `x`
checks and every reachable command in every `f a` checks, then so does
every reachable command in `x.flatMap f`.
-/
theorem AllSafe.flatMap {α β : Type} {env : CapEnv} {x : CapM α}
    {f : α → CapM β} (hx : AllSafe env x)
    (hf : ∀ a, AllSafe env (f a)) :
    AllSafe env (x.flatMap f) := by
  induction hx with
  | pure a =>
      -- (.pure a).flatMap f = f a
      exact hf a
  | cons cmd k hcheck _ ihk =>
      -- (.cons cmd k).flatMap f = .cons cmd (fun b => (k b).flatMap f)
      exact AllSafe.cons cmd _ hcheck (fun b => ihk b)

/-
The full soundness theorem: `SafeProg env prog` implies every reachable
command of `prog` passes the cap check. This closes the `.error e`
branch of `CapM.run` not just at the head but at every recursive call.
-/
theorem SafeProg.allSafe {α : Type} {env : CapEnv} {prog : CapM α}
    (h : SafeProg env prog) : AllSafe env prog := by
  induction h with
  | pureSafe _ a => exact AllSafe.pure a
  | readSafe _ c hv ha =>
      unfold CapM.read
      refine AllSafe.cons (CapCmd.read c) CapM.pure ?_ ?_
      · simp [CapCmd.check, CapEnv.isValid_of_valid hv, ha]
      · intro b; exact AllSafe.pure b
  | writeSafe _ c s hv ha =>
      unfold CapM.write
      refine AllSafe.cons (CapCmd.write c s) CapM.pure ?_ ?_
      · simp [CapCmd.check, CapEnv.isValid_of_valid hv, ha]
      · intro b; exact AllSafe.pure b
  | deleteSafe _ c hv ha =>
      unfold CapM.delete
      refine AllSafe.cons (CapCmd.delete c) CapM.pure ?_ ?_
      · simp [CapCmd.check, CapEnv.isValid_of_valid hv, ha]
      · intro b; exact AllSafe.pure b
  | flatMapSafe _ _ _ _ ih1 ih2 =>
      exact AllSafe.flatMap ih1 ih2

/- ===========================================================
   Interpreter
   =========================================================== -/

/-
`CapM.run` now delegates every cap-layer decision to `CapCmd.check`.
The only branches that remain in `IO` are the actual filesystem calls
and the recursive continuation. If `SafeProg env prog` holds then the
`.error e` branch below is unreachable (see `SafeProg.checkHead_ok`).
-/
  partial def CapM.run (env : CapEnv) : CapM α → IO (Except CapError α)
    | .pure a => return .ok a
    | .cons cmd k =>
      match CapCmd.check env cmd with
      | .error e => return .error e
      | .ok _ =>
        match cmd with
        | .read c =>
          match c.resource with
          | .file path => do
            let contents ← IO.FS.readFile path
            CapM.run env (k contents)
        | .write c s =>
          match c.resource with
          | .file path => do
            IO.FS.writeFile path s
            CapM.run env (k ())
        | .delete c =>
          match c.resource with
          | .file path => do
            IO.FS.removeFile path
            CapM.run env (k ())

  def CapM.runSafe (env : CapEnv) (prog : CapM α) (_h : SafeProg env prog) :
      IO (Except CapError α) :=
    CapM.run env prog
