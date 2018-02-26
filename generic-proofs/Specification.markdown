A (half-formal, half-hand-wavey) document on how we should reflect type class instances.

The simplest possible example is this:

```haskell
{-@
class Foo a where
  reflect bar :: a -> Int
  unused :: a
@-}
class Foo a where
  bar :: a -> Int

instance Foo Int where
  bar x = x
  unused = 42
```

This is what it might look in the surface syntax. At the Core level, this would more closely resemble the following:

```haskell
data Foo a = C:Foo
  { bar :: a -> Int
  , unused :: a
  }

-- Or, to be more precise:

bar :: forall a. Foo a -> a -> Int
bar = \ (@ a) (d :: Foo a) ->
  case d of _ { C:Foo x _ -> x } 

$cbar_Int :: Int -> Int
$cbar_Int = \(x :: Int) -> x

$cunused_Int :: Int
$cunused_Int = I# 42#

$dFooInt :: Foo Int
$dFooInt = C:Foo @Int $cbar_Int $cunused_Int
```

For each class method in `Foo` that is marked as `reflect`, we explicitly generate an `assume`:

```haskell
{-@ assume bar :: d:Foo a -> x:a -> {v:Int | v = bar d x} @-}
```

This integrates quite naturally with LH's existing machinery. There is a wrinkle with actually finding the `bar` function to attach this too—more on this in a moment.

For each instance, we take each reflected method and generate the corresponding reflected definition using the following quasi-syntax:

```haskell
{-@ (bar $dFooInt) :: x:Int -> {v:Int |    v = bar $dFooInt x
                                        && v = x } @-} 
```

Note that there are two parts to the reflected definition:

* The `v = bar $dFooInt x` part, which is just to link up the returned value `v` with the invocation of `bar` itself.
* The `v = x` part. This corresponds to the particular implementation of `bar`, `\x -> x`.

I use the phrase "quasi-syntax", since you can't normally write a LH annotation for a partially applied function like this. To make something like what is pictured above a reality, we will have to bake in special typing rules for class methods applied to dictionary arguments.

I don't think this is too objectionable, however. After all, the dictionary argument does not appear in the surface syntax, so a user would intuitively expect `bar` to have the type we wrote anyways (just not with the explicit dictionary).
