import Std.Data.HashMap
import AdventOfCode.Common.Result

-- A Path is a list of directory names starting from the root
def Path: Type := List String.Slice

-- A Directory can contain more directories (described by the path to reach them)
-- or files (which have a size)
inductive DirContents where
  | Dir (path: Path): DirContents
  | File (size: Nat): DirContents

instance : ToString DirContents where
  toString content := match content with
    | DirContents.Dir path => path.toString
    | DirContents.File size => ToString.toString size

def parseDirContents(line: String.Slice) (wd: Path): Result DirContents :=
  if line.startsWith "dir " then
    match (line.split " ").toList with
    | _ :: name :: [] => Except.ok (DirContents.Dir (name :: wd))
    | _ => Except.error "Unexpected dir line formatting"
  else match (line.split " ").toList with
    | size :: _ :: [] => match size.toNat? with
      | some size => Except.ok (DirContents.File size)
      | none => Except.error "Failed to parse number in file line"
    | _ => Except.error "Unexpected file line formatting"

def FileSystem: Type := Std.HashMap (List String.Slice) (Array DirContents)

instance : ToString FileSystem where
  toString fs := fs.toList.toString

-- Keep track of the current working directory and known file system so far
-- as we traverse the input.
structure TraverseState where
  wd: Path
  fs: FileSystem

-- Update the contents of a directory to include a new item.
def insertContent (new_content: DirContents) (current: Option (Array DirContents)): Option (Array DirContents) :=
  match current with
  | none => some #[new_content]
  | some existing => existing.push new_content

-- Update the state based on a line of input.
def handleLine (state: TraverseState) (line: String.Slice): Result TraverseState :=
  if line == "$ ls" then
    Except.ok state
  else if line == "$ cd .." then
    match state.wd with
    | _ :: tail => Except.ok ⟨ tail, state.fs ⟩
    | [] => Except.error "Cannot move up from the root!"
  else if line.startsWith "$ cd" then
    match (line.split " ").toList with
    | _ :: _ :: name :: [] => Except.ok ⟨ name :: state.wd, state.fs ⟩
    | _ => Except.error "Unexpected cd command formatting"
  else (parseDirContents line state.wd).map (
      fun content =>
        let updated_fs := state.fs.alter state.wd (insertContent content)
        ⟨ state.wd, updated_fs ⟩
    )

-- Parse the file system from the given input.
def parseFS(input: String): Result FileSystem :=
  let defaultState: TraverseState := ⟨ [], Std.HashMap.ofList [] ⟩
  let state := (input.trimAscii.split "\n").foldM handleLine defaultState
  state.map (fun x => x.fs)

-- Calculate the total size of a directory (including the size of sub-directories).
--
-- TODO: Definition must be partial because the current model
-- does not rule out the possibility of loops (directories that contain themselves)
-- since all paths are absolute. Maybe there is a better way to capture the tree
-- structure and then prove the termination of this function?
partial def sizeOfDir (path: Path) (fs: FileSystem) (cache: Std.HashMap (List String.Slice) Nat): Nat × (Std.HashMap (List String.Slice) Nat) :=
  match cache.get? path with
  | some size => (size, cache)
  | none =>
    let contents := fs.getD path #[]
    match contents.foldl (
      fun acc content => match acc with
      | (sizeAcc, cacheAcc) => match content with
        | DirContents.Dir path => match sizeOfDir path fs cacheAcc with
          | (dirSize, updatedCache) => (sizeAcc + dirSize, updatedCache.insert path dirSize)
        | DirContents.File size => (sizeAcc + size, cacheAcc)
    ) (0, cache) with
    | (totalSize, updatedCache) => (totalSize, updatedCache.insert path totalSize)

-- Compute sizes of all directories by starting at the root.
def computeSizes (fs: FileSystem): Std.HashMap (List String.Slice) Nat :=
  match sizeOfDir ["/"] fs (Std.HashMap.ofList []) with
  | (_, cache) => cache

def part1Solution(input: String): Result Nat := (parseFS input).map (
  fun fs =>
    let sizes := computeSizes fs
    (sizes.valuesIter.filter (fun x => x ≤ 100000)).fold Nat.add 0
)

def part2Solution(input: String): Result Nat := do
  let fs <- parseFS input
  let sizes := computeSizes fs
  let usedSpace <- getOrErr (sizes.get? ["/"]) "No size for /"
  let freeSpace := 70000000 - usedSpace
  let requiredDelete := 30000000 - freeSpace
  pure ((sizes.valuesIter.filter (fun x => requiredDelete ≤ x)).fold min 70000000)
