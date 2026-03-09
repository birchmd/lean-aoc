def Result(α : Type): Type := Except String α

instance : Applicative Result where
  pure := Except.ok
  seq mf mx := mf.bind (fun f => (mx ()).map f)

instance : Bind Result where
  bind := Except.bind

instance : Monad Result where

instance : MonadAttach Result where
  CanReturn x a :=
    let y: ExceptT String Id _ := x
    MonadAttach.CanReturn y a
  attach x :=
    let y: ExceptT String Id _ := x
    MonadAttach.attach y

instance [ToString α] : ToString (Result α) where
  toString r := match r with
  | Except.error e => e
  | Except.ok x => ToString.toString x

def getOrErr (mx: Option α) (e: String): Result α :=
  (mx.map Except.ok).getD (Except.error e)

def Result.ok (x: α): Result α := Except.ok x
