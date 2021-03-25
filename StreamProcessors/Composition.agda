module StreamProcessors.Composition where

open import Codata.Thunk as Thunk using (Thunk; force)

open import StreamProcessors.Core

infixl 4 _|>_ _♯|>_ _|>♯_ _♯|>♯_
infixr 4 _<|_

_|>_ : ∀  {i} {α} {A B C : Set α} → Pipe A B i → Pipe B C i → Pipe A C i
_♯|>_ : ∀  {i} {α} {A B C : Set α} → Thunk (Pipe A B) i → Pipe B C i → Thunk (Pipe A C) i
_|>♯_ : ∀  {i} {α} {A B C : Set α} → Pipe A B i → Thunk (Pipe B C) i → Thunk (Pipe A C) i
_♯|>♯_ : ∀  {i} {α} {A B C : Set α} → Thunk (Pipe A B) i → Thunk (Pipe B C) i → Thunk (Pipe A C) i
_ |> stop = stop
up |> yield value next = yield value (up |>♯ next)
stop |> demand onNext = stop
yield value next |> demand onNext = lazy (next ♯|>♯ onNext value)
demand onNext |> down@(demand _) = demand (λ value → onNext value ♯|> down)
lazy up |> down@(demand _) = lazy (up ♯|> down)
up |> lazy down = lazy (up |>♯ down)
(a ♯|> b) .force = a .force |> b
(a |>♯ b) .force = a |> b .force
(a ♯|>♯ b) .force = a .force |> b .force

_<|_ : ∀ {i} {α} {A B C : Set α} → Pipe B C i → Pipe A B i → Pipe A C i
down <| up = up |> down
