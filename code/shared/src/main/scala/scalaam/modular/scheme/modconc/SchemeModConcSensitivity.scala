package scalaam.modular.scheme.modconc

import scalaam.language.scheme._

trait SchemeModConcNoSensitivity extends SchemeModConcSemantics {
    type ComponentContext = Unit
    def allocCtx(exp: SchemeExp, env: Env, caller: Component) = ()
}