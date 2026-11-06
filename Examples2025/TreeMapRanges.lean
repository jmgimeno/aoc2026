import Std.Data.TreeMap

open Std

namespace Examples2025.TreeMapRanges

/-! ## BTreeMap: ordered lookups and ranges (day 9) -/
def tm : TreeMap Nat String := TreeMap.ofList [(1,"a"),(5,"b"),(9,"c")]
#eval tm.getEntryGE? 2
#eval tm.getEntryLE? 8
#eval (tm[2...=8]).toList

end Examples2025.TreeMapRanges
