namespace FSharpPlus

/// <summary> Computation type: Computations which update things.
/// <para/>   Binding strategy: Combines the updates of the subcomputations using <c>mappend</c>.
/// <para/>   Useful for: Definitions of Reader, Writer, State monads. </summary>
type Update<'s, 'u, 't> = Update of ('s -> ('u * 't))

[<RequireQualifiedAccess>]
module Update =
    let inline update< ^S, ^U when ^U : (static member Update: ^S * ^U -> ^S )> s a: ^S =
      (^U : (static member Update: ^S * ^U -> ^S) (s, a))

    let        run (Update x) = x                                       : 'S -> ('U * 'T)
    let        map   f (Update m) = 
        Update (fun s -> let (u, a: 'T) = m s in (u, f a))              : Update<'S, 'U, 'T>
    let inline bind  f (Update m) =
        Update (fun s ->
            let (u1, a: 'T) = m s in
            let (u2, b: 'T) = run (f a) (update s u1) in
            (append u1 u2, b))                                          : Update<'S, 'U, 'T>

    let inline apply (Update f) (Update x) =
        Update (fun s ->
            let (u1, f') = f s in
            let (u2, x') = x (update s u1) in
            (append u1 u2, f' x'))                                      : Update<'S, 'U, 'T>

    /// Return the state from the internals of the monad.
    let inline get () = Update (fun s -> (getEmpty (), s))              : Update<'S, 'U, 'S>

    /// Update the state with u inside the monad.
    let up u  = Update (fun _ -> (u, ()))                               : Update<'S, 'U, unit>

type Update with
    static member        Map   (x, f: _ -> _) = Update.map f x                 : Update<'S, 'U, 'T>
    static member inline Return a = Update (fun s -> (getEmpty (), a))         : Update<'S, 'U, 'T>
    static member inline Bind  (x, f: _ -> _) = Update.bind f x                : Update<'S, 'U, 'T>
    static member inline (<*>) (f, x: Update<'S, 'U, 'T>) = Update.apply f x   : Update<'S, 'U, 'T>
    static member inline get_Get() = Update.get ()                             : Update<'S, 'U, 'S>
    static member        Up u      = Update.up u                               : Update<'S, 'U, unit>

open FsControl

type UpdateT<'s, '``monad<'u * 't>``> = UpdateT of ('s -> '``monad<'u * 't>``)

[<RequireQualifiedAccess>]
module UpdateT =
    let run (UpdateT x): 'S -> '``Monad<'U * 'T>`` = x 

    let inline map (f : 'T -> 'V) (UpdateT (m : _ -> '``Monad<'U * 'T>``)) =
        UpdateT (m >> Map.Invoke (fun (u, x) -> (u, f x)))                                                                    : UpdateT<'S, '``Monad<'U * 'V>``>
    let inline apply (UpdateT f : UpdateT<'S, '``Monad<'U * ('T -> 'V)>``>) (UpdateT a : UpdateT<'S, '``Monad<'U * 'T>``>) =
        UpdateT (fun s -> f s >>= fun (g, t) -> Map.Invoke (fun (z, v) -> (g z, v)) (a t))                                    : UpdateT<'S, '``Monad<'U * 'V>``>
    let inline bind (f : 'T -> UpdateT<'S, '``Monad<'U * 'V>``>) (UpdateT m : UpdateT<'S, '``Monad<'U * 'T>``>) =
        UpdateT (fun s ->
            m s                               >>= (fun (u1, a) ->
            run (f a) (Update.update s u1)    >>= (fun (u2, b) ->
            result (append u1 u2, b))))                                                                                       : UpdateT<'S, '``Monad<'U * 'V>``>
    let inline result(x : 'T) =
        UpdateT (fun s -> result (getEmpty (), x))                                                                            : UpdateT<'S, '``Monad<'U * 'T>``>

type UpdateT with
    static member inline Return (x : 'T)                                                                             = UpdateT.result x       : UpdateT<'S, '``Monad<'U * 'T>``>
    static member inline Map    (x : UpdateT<'S, '``Monad<'U * 'T>``>, f : 'T -> 'V)                                 = UpdateT.map    f x     : UpdateT<'S, '``Monad<'U * 'V>``>
    static member inline (<*>)  (f : UpdateT<'S, '``Monad<'U * ('T -> 'V)>``>, x : UpdateT<'S, '``Monad<'U * 'T>``>) = UpdateT.apply  f x     : UpdateT<'S, '``Monad<'U * 'V>``>
    static member inline Bind   (x : UpdateT<'S, '``Monad<'U * 'T>``>, f : 'T -> UpdateT<'S, '``Monad<'U * 'V>``>)   = UpdateT.bind   f x     : UpdateT<'S, '``Monad<'U * 'V>``>

    static member inline MZero (output : UpdateT<'S, '``MonadPlus<'U * 'T>``>, impl : MZero)  = UpdateT (fun _ -> getMZero())     : UpdateT<'S, '``MonadPlus<'U * 'T>``>
    static member inline MPlus (UpdateT m, UpdateT n, impl : MPlus)                           = UpdateT (fun s -> m s <|> n s)    : UpdateT<'S, '``MonadPlus<'U * 'T>``>

    static member inline Lift (m : '``Monad<'T>``) = UpdateT (fun s -> m >>= (fun a -> result (getEmpty(), a)))      : UpdateT<'S,'``Monad<'U * 'T>``>

    static member inline LiftAsync (x : Async<'T>) = lift (liftAsync x)     : '``UpdateT<'S, 'MonadAsync<'T>>``
    
    static member inline get_Get()  = UpdateT (fun s -> result (s , s))     : UpdateT<'S, '``Monad<'U * 'S>``>
    static member inline Up (u: 'U) = UpdateT (fun _ -> result (u, ()))     : UpdateT<'S, '``Monad<'U * unit>``>

    (*
    static member inline Throw (x : 'E) = x |> throw |> lift
    static member inline Catch (m : UpdateT<'S, '``MonadError<'E1, 'U * 'T>``>, h: 'E1 -> _) = 
        UpdateT (fun s -> catch (UpdateT.run m s) (fun e -> UpdateT.run (h e) s))  : UpdateT<'S,'``MonadError<'E2, 'U * 'T>``>
    //*)
