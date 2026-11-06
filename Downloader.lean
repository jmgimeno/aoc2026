/-!
Downloads the input of one day into `data/dayNN.txt`, using `curl`.

It needs the `AOC_COOKIE` environment variable, which `just` loads from `.env`.
-/

/-- `day07` → `some 7` -/
def parseDay (s : String) : Option Nat := do
  guard (s.length == 5 && s.startsWith "day")
  (s.drop 3).toNat?

/-- The cookie goes through stdin, so it does not show up in the process arguments (`ps`). -/
def download (url cookie : String) (out : System.FilePath) : IO UInt32 := do
  let child ← IO.Process.spawn {
    cmd := "curl"
    args := #["--fail", "--silent", "--show-error", "--config", "-",
              "--user-agent", "github.com/jmgimeno/aoc2026 downloader",
              "--output", out.toString, url]
    stdin := .piped
  }
  let (stdin, child) ← child.takeStdin
  stdin.putStr s!"header = \"Cookie: session={cookie}\"\n"
  stdin.flush
  child.wait

def main (args : List String) : IO UInt32 := do
  let some day := args.head?.bind parseDay
    | IO.eprintln "usage: lake exe downloader dayNN"; return 1
  let some cookie ← IO.getEnv "AOC_COOKIE"
    | IO.eprintln "AOC_COOKIE is not set"; return 1
  IO.FS.createDirAll "data"
  let out : System.FilePath := "data" / s!"day{if day < 10 then "0" else ""}{day}.txt"
  let code ← download s!"https://adventofcode.com/2026/day/{day}/input" cookie out
  if code == 0 then
    IO.println s!"Day {day} downloaded."
  else
    IO.eprintln s!"Error downloading day {day}"
  return code
