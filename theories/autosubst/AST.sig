-- Universe levels
level : Type

-- Syntax

term(var) : Type

Sort : level -> term

Pi : level -> level -> term -> (bind term in term) -> term
lam : level -> level -> term -> (bind term in term) -> (bind term in term) -> term
app : level -> level -> term -> (bind term in term) -> term -> term -> term
Nat : term 
zero : term 
succ : term -> term 
rec : level -> (bind term in term) -> term -> (bind term , term in term) -> term -> term
box : term