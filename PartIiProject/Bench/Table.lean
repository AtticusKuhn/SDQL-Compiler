import PartIiProject.Bench.Common
import Std

namespace PartIiProject.Bench

structure MsComparisonRow where
  name : String
  leftMs : Nat
  rightMs : Nat

def printMsComparisonTable
    (title : String)
    (leftLabel rightLabel ratioLabel : String)
    (rows : List MsComparisonRow)
    (preamble : List String := [])
    (nameHeader : String := "case")
    (totalLabel : String := "TOTAL")
    (colW : Nat := 12) : IO Unit := do
  if rows.isEmpty then
    IO.println "No benchmarks ran."
    return

  let nameW := rows.foldl (fun w r => max w r.name.length) nameHeader.length

  IO.println title
  for l in preamble do
    IO.println l

  IO.println (padRight nameW nameHeader ++ "  " ++
    padLeft colW leftLabel ++ "  " ++
    padLeft colW rightLabel ++ "  " ++
    padLeft colW ratioLabel)
  IO.println (String.mk (List.replicate (nameW + 2 + colW*3 + 4) '-'))

  for r in rows do
    IO.println (padRight nameW r.name ++ "  " ++
      padLeft colW s!"{r.leftMs}ms" ++ "  " ++
      padLeft colW s!"{r.rightMs}ms" ++ "  " ++
      padLeft colW (ratioString r.rightMs r.leftMs))

  let totalLeft := rows.foldl (fun s r => s + r.leftMs) 0
  let totalRight := rows.foldl (fun s r => s + r.rightMs) 0
  IO.println (String.mk (List.replicate (nameW + 2 + colW*3 + 4) '-'))
  IO.println (padRight nameW totalLabel ++ "  " ++
    padLeft colW s!"{totalLeft}ms" ++ "  " ++
    padLeft colW s!"{totalRight}ms" ++ "  " ++
    padLeft colW (ratioString totalRight totalLeft))

end PartIiProject.Bench

