import LeanCbs

open Lean (Json)

/-
Smoke test for the v0 parser pipeline.

Mints three caps over files in `tmp_demo/`, parses six hand-crafted JSON
programs, verifies them, and (on success) executes via `CapM.runSafe`
so the actual IO happens. Covers each DslNode kind plus the two attack
scenarios from §5.3.
-/

def runDemo (env : CapEnv) (m : ResolveMap)
    (label : String) (jsonStr : String) : IO Unit := do
  IO.println s!"--- {label}"
  match Json.parse jsonStr with
  | .error e => IO.println s!"  json parse error: {e}"
  | .ok j =>
      match parseAndVerify env m j with
      | .error e =>
          IO.println s!"  rejected: {repr e}"
      | .ok vp =>
          IO.println "  verified ✓"
          try
            let runResult ← CapM.runSafe env vp.prog vp.hSafe
            match runResult with
            | .ok _    => IO.println "  ran ✓"
            | .error e => IO.println s!"  cap-layer error (unreachable on SafeProg): {repr e}"
          catch e =>
            IO.println s!"  IO error: {e}"

def main : IO Unit := do
  -- Set up working files
  let workdir : System.FilePath := "tmp_demo"
  IO.FS.createDirAll workdir
  IO.FS.writeFile (workdir / "report.txt") "demo report contents\n"
  IO.FS.writeFile (workdir / "trash.txt")  "to be deleted\n"

  -- Mint caps over those files
  let env₀ : CapEnv := { nextId := 0, wallet := [], revoked := [] }
  let (readCap,   env₁) := env₀.issue (.file "tmp_demo/report.txt")  .read
  let (writeCap,  env₂) := env₁.issue (.file "tmp_demo/summary.txt") .write
  let (deleteCap, env)  := env₂.issue (.file "tmp_demo/trash.txt")   .delete
  let m : ResolveMap :=
    [ ("report_read",   readCap)
    , ("summary_write", writeCap)
    , ("trash_delete",  deleteCap) ]

  runDemo env m "read program (reads report.txt)"
    "{\"kind\":\"read\",\"capability\":\"report_read\"}"

  runDemo env m "write program (writes summary.txt)"
    "{\"kind\":\"write\",\"capability\":\"summary_write\",\"contents\":\"hello from v0\\n\"}"

  runDemo env m "seq program (read report, write summary)"
    "{\"kind\":\"seq\",\"first\":{\"kind\":\"read\",\"capability\":\"report_read\"},\"rest\":{\"kind\":\"write\",\"capability\":\"summary_write\",\"contents\":\"from seq\\n\"}}"

  runDemo env m "delete program (deletes trash.txt)"
    "{\"kind\":\"delete\",\"capability\":\"trash_delete\"}"

  runDemo env m "attack A: unknown capability name"
    "{\"kind\":\"delete\",\"capability\":\"secrets_delete\"}"

  runDemo env m "attack B: authority mismatch"
    "{\"kind\":\"delete\",\"capability\":\"report_read\"}"

  IO.println "\nFinal state of tmp_demo/:"
  let entries ← workdir.readDir
  for e in entries do
    let contents ← IO.FS.readFile e.path
    IO.println s!"  {e.fileName}: {contents.trim}"
