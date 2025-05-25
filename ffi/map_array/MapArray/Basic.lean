structure MapOptions where
  addend : Int32
  multiplicand : Int32
deriving Repr

@[export my_map]
def map (options : MapOptions) (arr : Array UInt8) : Array Int32 :=
  arr.map (fun x => (x.toInt8.toInt32 + options.addend) * options.multiplicand)
