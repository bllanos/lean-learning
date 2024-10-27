-- # Examples

#check 1.2
#check -454.2123215
#check 0
#check 0.0
#check (0 : Float)
#check 0 + 4.5
-- #check (0 : Nat) + 4.5

structure Point where
  x : Float
  y : Float
deriving Repr

def origin : Point := { x := 0.0, y := 0.0 }
#eval origin
#eval origin.x
#eval origin.y

def addPoints (p1 p2 : Point) : Point :=
  { x := p1.x + p2.x, y := p1.y + p2.y }
#eval addPoints { x := 1.5, y := 32 } { x := -8, y := 0.2 }

def distance (p1 : Point) (p2 : Point) : Float :=
  Float.sqrt (((p1.x - p2.x) ^ 2.0) + ((p1.y - p2.y) ^ 2.0))
#eval distance { x := 1, y := 2 } { x := 3, y := 5 }
#eval 3.605551 ^ 2

structure Point3D where
  x : Float
  y : Float
  z : Float
deriving Repr

def origin3D : Point3D := { x := 0.0, y := 0.0, z := 0.0 }
#check ({ x := 0.0, y := 0.0, z := 0.0 } : Point3D)
#check { x := 0.0, y := 0.0, z := 0.0 : Point3D }

def zeroX (p : Point) : Point :=
  { x := 0.0, y := p.y }

def zeroX2 (p : Point) : Point :=
  { p with x := 0.0 }

def fourAndThree : Point :=
  { x := 4.3, y := 3.4 }
#eval fourAndThree
#eval zeroX fourAndThree
#eval fourAndThree

#check Point.mk 1.5 2.8
#check Point.mk
#check (Point.mk)

structure Point2 where
  point2 ::
  x : Float
  y : Float
deriving Repr

#check (Point2.point2)
#check (Point2.x)
#check (Point2.y)

#eval origin.x
#eval Point.x fourAndThree

def Point2.product (p : Point2) : Float :=
  p.x * p.y
def newPoint := { x := 3.0, y := 6.0 : Point2 }
#eval newPoint.product

#eval "one string".append " and another"

def Point.modifyBoth (f : Float → Float) (p : Point) : Point :=
  { x := f p.x, y := f p.y }

#eval fourAndThree.modifyBoth Float.floor

-- # Exercises

structure RectangularPrism where
  rectangularPrism ::
  height: Float
  width: Float
  depth: Float
deriving Repr

def RectangularPrism.volume (prism : RectangularPrism) : Float :=
  prism.height * prism.width * prism.depth
#eval { height := 2, width := 3, depth := 4 : RectangularPrism }.volume

structure Segment where
  segment ::
  start : Point
  endpoint : Point
deriving Repr

def Segment.length (s : Segment) : Float :=
  distance s.start s.endpoint

#eval { start := { x := 1, y := 2 }, endpoint := { x := 3, y := 5 } : Segment }.length

structure Hamster where
  name : String
  fluffy : Bool
#check Hamster.fluffy
#check Hamster.name
#check Hamster.mk

structure Book where
  makeBook ::
  title : String
  author : String
  price : Float
#check Book.makeBook
