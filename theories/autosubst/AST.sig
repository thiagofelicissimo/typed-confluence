-- Universe levels
level : Type

-- Syntax

term(var) : Type

Sort : level -> term

Pi : level -> level -> term -> (bind term in term) -> term
lam : level -> level -> term -> (bind term in term) -> (bind term in term) -> term
app : level -> level -> term -> (bind term in term) -> term -> term -> term

Sigma : level -> level -> term -> (bind term in term) -> term
pair : level -> level -> term -> (bind term in term) -> term -> term -> term
pi1 : level -> level -> term -> (bind term in term) -> term -> term
pi2 : level -> level -> term -> (bind term in term) -> term -> term

Nat : term 
zero : term 
succ : term -> term 
rec : level -> (bind term in term) -> term -> (bind term , term in term) -> term -> term

box : term

Eq : level -> term -> term -> term -> term
J : level -> level -> term -> term -> (bind term in term) -> term -> term -> term -> term

Lift : level -> term -> term 
lift : level -> term -> term -> term
lower : level -> term -> term -> term

-- observational equality
cast    : level -> term -> term -> term -> term -> term
injpi1  : level -> level -> term -> term -> (bind term in term) -> (bind term in term) -> term -> term
injpi2  : level -> level -> term -> term -> (bind term in term) -> (bind term in term) -> term -> term -> term
