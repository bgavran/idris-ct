module Utils

public export
cong2 : (f : t -> u -> v) -> a = b -> c = d -> f a c = f b d
cong2 f Refl Refl = Refl

public export 
swap : (a, b) -> (b, a)
swap (x, y) = (y, x)
