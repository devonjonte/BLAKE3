import ReadingList
import PushContract
import MergeContract
import LevelsContract

/-! What a reader of each design's contracts must read: the stack's three (`push`, `merge`, `add`) and the
levels' two (`ladd`, `lroot`). No theorem is about the levels' code yet; these two statements are true by
`rfl` and exist only so that `#reading_defs` can walk what the contracts are made of (no machine, and
nothing of "meets"). -/

theorem Reading.stack : (@Push.byteContract, @Merge.byteContract, @Add.byteContract) =
    (@Push.byteContract, @Merge.byteContract, @Add.byteContract) := rfl
theorem Reading.levels : (@Ladd.byteContract, @Lroot.byteContract) = (@Ladd.byteContract, @Lroot.byteContract) := rfl

#reading_defs Reading.stack
#reading_defs Reading.levels
