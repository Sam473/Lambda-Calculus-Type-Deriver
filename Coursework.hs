
--------------------------------------------
--                                        --
-- CM20256/CM50262 Functional Programming --
--                                        --
--         Coursework 2020/2021           --
--                                        --
--------------------------------------------

------------------------- Auxiliary functions

find :: (Show a,Eq a) => a -> [(a,b)] -> b
find x [] = error ("find: " ++ show x ++ " not found")
find x ((y,z):zs)
  | x == y    = z
  | otherwise = find x zs


merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
    | x == y    = x : merge xs ys
    | x <= y    = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys

minus :: Ord a => [a] -> [a] -> [a]
minus xs [] = xs
minus [] ys = []
minus (x:xs) (y:ys)
    | x <  y    = x : minus    xs (y:ys)
    | x == y    =     minus    xs    ys
    | otherwise =     minus (x:xs)   ys


------------------------- Lambda-terms

type Var = String

data Term =
    Variable Var
  | Lambda   Var  Term
  | Apply    Term Term
  deriving Eq


instance Show Term where
  show = f 0
    where
      f i (Variable x) = x
      f i (Lambda x m) = if i /= 0 then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ". " ++ f 0 m 
      f i (Apply  n m) = if i == 2 then "(" ++ s ++ ")" else s where s = f 1 n ++ " " ++ f 2 m

free :: Term -> [Var]
free (Variable x) = [x]
free (Lambda x n) = free n `minus` [x]
free (Apply  n m) = free n `merge` free m


------------------------- Types

infixr 5 :->

type Atom = String
data Type = At Atom | Type :-> Type
  deriving Eq

instance Show Type where
  show (At a)       = a
  show (At a :-> s) = a ++ " -> " ++ show s
  show    (t :-> s) = "(" ++ show t ++ ") -> " ++ show s


atoms :: [Atom]
atoms = map (:[]) ['a'..'z'] ++ [ a : show i | i <- [1..], a <- ['a'..'z'] ]

t1 :: Type
t1 = At "a" :-> At "b"

t2 :: Type
t2 = (At "c" :-> At "d") :-> At "e"

t3 :: Type
t3 = At "a" :-> At "c" :-> At "c"


------------------------- Assignment 1

occurs :: Atom -> Type -> Bool
occurs x (At y) = x == y
occurs x (y :-> ys) = occurs x ys || occurs x y

findAtoms :: Type -> [Atom]
findAtoms (At x) = [x]
findAtoms (x :-> xs) = merge (findAtoms x)  (findAtoms xs)


------------------------- Type substitution

type Sub = (Atom,Type)

s1 :: Sub
s1 = ("a", At "e")

s2 :: Sub
s2 = ("e", At "b" :-> At "c")

s3 :: Sub
s3 = ("c", At "a" :-> At "a")


------------------------- Assignment 2

sub :: Sub -> Type -> Type
sub x (y :-> ys) = sub x y :-> sub x ys
sub x (At y) 
  | fst x == y = snd x
  | otherwise = At y

subs :: [Sub] -> Type -> Type
subs [x] y = sub x y
subs x y = sub (head x) (subs (tail x)  y)


------------------------- Unification

-- pair of types where
type Upair = (Type,Type)
type State = ([Sub],[Upair])

u1 :: Upair
u1 = (t1,At "c")

u2 :: Upair
u2 = (At "a" :-> At "a",At "a" :-> At "c")

u3 :: Upair
u3 = (t1,t2)

u4 :: Upair
u4 = (t2,t3)

st1 :: State
st1 = ([],[u1,u2])


------------------------- Assignment 3

-- for each in list, for each pair, substitute
sub_u :: Sub -> [Upair] -> [Upair]
sub_u _ [] = []
sub_u x (y:ys) = (sub x (fst y), sub x (snd y)) : (sub_u x ys)

-- creating a list of subs from unification pairs
step :: State -> State
step (y,(x :-> xt, xx :-> xxt):xs) = (y, (x,xx):(xt,xxt):xs)
step (y,(At x, At xx):xs) 
  | x == xx = (y,xs)
step (y,(At x, xx):xs) 
  | occurs x xx = error "Fail"
  | occurs x xx == False = ((x,xx):y, (sub_u (x,xx) xs))
step (y,(x, At xx):xs) 
  | occurs xx x = error "Fail"
  | occurs xx x == False = ((xx,x):y, (sub_u (xx,x) xs))

-- apply step function until run out of unification pairs to build up list of subs
unify :: [Upair] -> [Sub]
unify y = unifies ([], y)
  where unifies (x, []) = x
        unifies (x, y) = unifies (step (x,y)) 

------------------------- Assignment 4

type Context   = [(Var, Type)]
type Judgement = (Context, Term, Type)

data Derivation = 
    Axiom Judgement 
  | Application Judgement Derivation Derivation
  | Abstraction Judgement Derivation

n1 = Apply (Lambda "x" (Variable "x")) (Variable "y")


d1 = Application ([("y",At "a")], n1 , At "a") (
       Abstraction ([("y",At "a")],Lambda "x" (Variable "x"),At "a" :-> At "a") (
         Axiom ([("x",At "a"),("y",At "a")],Variable "x",At "a")
     ) ) (
       Axiom ([("y",At "a")], Variable "y", At "a")
     )

d2 = Application ([("y",At "b")],Apply (Lambda "x" (Apply (Variable "x") (Variable "y"))) (Lambda "z" (Variable "z")),At "a") (
       Abstraction ([("y",At "b")],Lambda "x" (Apply (Variable "x") (Variable "y")),At "c") (
         Application ([("x",At "d"),("y",At "b")],Apply (Variable "x") (Variable "y"),At "e") (
           Axiom ([("x",At "d"),("y",At "b")],Variable "x",At "f")
         ) (
           Axiom ([("x",At "d"),("y",At "b")],Variable "y",At "g")
     ) ) ) (
       Abstraction ([("y",At "b")],Lambda "z" (Variable "z"),At "h") (
         Axiom ([("z",At "i"),("y",At "b")],Variable "z",At "j")
     ) )


-- return judgement for each possible derivation
conclusion :: Derivation -> Judgement
conclusion (Axiom x) = x
conclusion (Application x y z) = x
conclusion (Abstraction x y) = x


-- change type with substitution
subs_ctx :: [Sub] -> Context -> Context
subs_ctx _ [] = []
subs_ctx x (y:ys) = (fst y, subs x (snd y)) : (subs_ctx x ys)

--substitute type and context
subs_jdg :: [Sub] -> Judgement -> Judgement
subs_jdg s (x, y, z) = (subs_ctx s x, y,subs s z)

--do the recursive pattern matching
subs_der :: [Sub] -> Derivation -> Derivation
subs_der s (Axiom x) = Axiom (subs_jdg s x)
subs_der s (Application x y z) = Application (subs_jdg s x) (subs_der s y) (subs_der s z)
subs_der s (Abstraction x y) = Abstraction (subs_jdg s x) (subs_der s y)


------------------------- Typesetting derivations


instance Show Derivation where
  show d = unlines (reverse strs)
    where
      (_,_,_,strs) = showD d

      showC :: Context -> String
      showC [] = []
      showC [(x,t)]    = x ++ ": " ++ show t
      showC ((x,t):cx) = x ++ ": " ++ show t  ++ " , " ++ showC cx

      showJ :: Judgement -> String
      showJ ([],n,t) =              "|- " ++ show n ++ " : " ++ show t
      showJ (cx,n,t) = showC cx ++ " |- " ++ show n ++ " : " ++ show t

      showL :: Int -> Int -> Int -> String
      showL l m r = replicate l ' ' ++ replicate m '-' ++ replicate r ' '

      showD :: Derivation -> (Int,Int,Int,[String])
      showD (Axiom j) = (0,k,0,[s,showL 0 k 0]) where s = showJ j; k = length s
      showD (Abstraction j d)   = addrule (showJ j) (showD d)
      showD (Application j d e) = addrule (showJ j) (sidebyside (showD d) (showD e))

      addrule :: String -> (Int,Int,Int,[String]) -> (Int,Int,Int,[String])
      addrule x (l,m,r,xs)
        | k <= m     = (ll,k,rr, (replicate ll ' ' ++ x ++ replicate rr ' ') : showL  l m r  : xs)
        | k <= l+m+r = (ll,k,rr, (replicate ll ' ' ++ x ++ replicate rr ' ') : showL ll k rr : xs)
        | otherwise  = (0,k,0, x : replicate k '-' : [ replicate (-ll) ' ' ++ y ++ replicate (-rr) ' ' | y <- xs])
        where
          k = length x
          i = div (m - k) 2
          ll = l+i
          rr = r+m-k-i

      extend :: Int -> [String] -> [String]
      extend i strs = strs ++ repeat (replicate i ' ')

      sidebyside :: (Int,Int,Int,[String]) -> (Int,Int,Int,[String]) -> (Int,Int,Int,[String])
      sidebyside (l1,m1,r1,d1) (l2,m2,r2,d2)
        | length d1 > length d2 = ( l1 , m1+r1+2+l2+m2 , r2 , [ x ++ "  " ++ y | (x,y) <- zip d1 (extend (l2+m2+r2) d2)])
        | otherwise             = ( l1 , m1+r1+2+l2+m2 , r2 , [ x ++ "  " ++ y | (x,y) <- zip (extend (l1+m1+r1) d1) d2])


------------------------- Assignment 5

{-- 
*Take a term
*Parse through it to put all the bits into a judgement, filling context with free variables
*Pass that judgement to aux which then turns the judgements into derivations

data Term =
    Variable Var
  | Lambda   Var  Term
  | Apply    Term Term
  deriving Eq

n1 = Apply (Lambda "x" (Variable "x")) (Variable "y")

type Context   = [(Var, Type)] use a list comprehension list of pair x, e (free x)
type Judgement = (Context, Term, Type)

data Derivation = 
    Axiom Judgement 
  | Application Judgement Derivation Derivation
  | Abstraction Judgement Derivation

in aux pattern match for each term
if varibale make axiom, lambda abstraction
  recurse for 

--}

derive0 :: Term -> Derivation
derive0 x = aux (zip (free x) ([At ""]),  x, At "")
  where
    aux :: Judgement -> Derivation
    aux (x,Variable y,z) = Axiom (x,Variable y,z)
    aux (x, Lambda y ys,z) = Abstraction (x,Lambda y ys,z) (aux ((y, At ""):x, ys, z))
    aux (x,Apply y ys,z) = Application (x,Apply y ys,z) (aux (x, y, z)) (aux (x, ys, z))
{--

Base off derive 0
instead of empty atoms, assign each variable a type, free variables in context given a distinct atom
assign distinct atoms to the right variables

construct context same way

get rest of the atoms for the aux function as well as judgement

for the abstraction, when you call aux again add abstracted value with new atom into context

 aux ([(i,j) | i <- free x, j <- atoms],  x, atoms)

 aux atoms ([(i, At j) | i <- free x, j <- tail atoms],  x, At (head atoms))
--}

derive1 :: Term -> Derivation -- fix the tail tail atoms thing to work for all cases
derive1 x = aux (drop (length (free x)+1) atoms) ((zip (free x) (map At (tail atoms))),  x, At (head atoms))
  where
    aux :: [Atom] -> Judgement -> Derivation 
    aux a (x, Variable y,z) = Axiom (x,Variable y,z)
    aux a (x, Lambda y ys,z) = Abstraction (x,Lambda y ys,z) (aux (tail a) (((y, At (head a)) :x), ys, At (head (tail a))))
    aux a (x, Apply y ys,z) = Application (x,Apply y ys,z) (aux (tail (evens a)) (x, y, At (head (evens a)))) (aux (tail (odds a)) (x, ys, At (head (odds a)))) -- Split into distinct atom stream for each
    evens xs = [x | (i, x) <- zip [0..] xs, even i]
    odds xs = [x | (i, x) <- zip [0..] xs, odd i]

{--
type Context   = [(Var, Type)] use a list comprehension list of pair x, e (free x)
type Judgement = (Context, Term, Type)

data Derivation = 
    Axiom Judgement 
  | Application Judgement Derivation Derivation
  | Abstraction Judgement Derivation

n1 = Apply (Lambda "x" (Variable "x")) (Variable "y")

data Term =
    Variable Var
  | Lambda   Var  Term
  | Apply    Term Term
  deriving Eq

data Type = At Atom | Type :-> Type
  deriving Eq

type Upair = (Type,Type)

Takes the unification pairs from derivation.

*Take derivation
*Extract unification pairs using incomplete rules and unification pairs 
when pass variable get type of variable and type of term
Deconstruct and pattern match to get the unification pairs

FOR APPLICATION:
 - GET THE BETA FROM 

second part 
type of abstracted variable :-> type of M

look in judgements for types of terms

conclusion function to get judgement of m and n

Think the problem is with head in axiom and abstraction

find :: (Show a,Eq a) => a -> [(a,b)] -> b
find x [] = error ("find: " ++ show x ++ " not found")
find x ((y,z):zs)
  | x == y    = z
  | otherwise = find x zs

find variable context

--}

upairs :: Derivation -> [Upair]
upairs (Axiom x) = [(third x, find (snd  x) (myfst x))]
  where third (_, _, z) = z
        myfst (x, _, _) = x
        mysnd (_, y, _) = y
upairs (Abstraction x y) = ((third x),  (snd (head (myfst (conclusion y))) :-> (third (conclusion y)))) : upairs y
  where third (_, _, z) = z
        myfst (x, _, _) = x
upairs (Application x y z) = (third (conclusion y), (third (conclusion z)) :-> (third x)) : (umerge (upairs y) (upairs z))
  where third (_, _, z) = z
        umerge :: [a] -> [a] -> [a]
        umerge xs     []     = xs
        umerge []     ys     = ys
        umerge (x:xs) (y:ys) = x : y : umerge xs ys

{--
data Term =
    Variable Var
  | Lambda   Var  Term
  | Apply    Term Term
  deriving Eq

n1 = Apply (Lambda "x" (Variable "x")) (Variable "y")

type Context   = [(Var, Type)] use a list comprehension list of pair x, e (free x)
type Judgement = (Context, Term, Type)

data Derivation = 
    Axiom Judgement 
  | Application Judgement Derivation Derivation
  | Abstraction Judgement Derivation


*Take term
*Use derive1 to produce a type derivation for it 
*Extract unification pairs from the derivation
*unify the pairs with unify function to get substitutions
*use subs der to apply the substitutions to derivation

AFTER:
*Check if result is valid or not, if not throw error
--}

derive :: Term -> Derivation
derive = undefined

