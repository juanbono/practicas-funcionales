module GenericHaskell where
import Data.Generics
data Country = Argentina | India | Colombia
data BrewMethod = BrewMethod1 | BrewMethod2 | BrewMethod3

data Coffee = MkCoffee { coffeeBeans :: String
                       , coffeeOriginCountry :: Country
                       , coffeeBrewMethod :: BrewMethod
                       }
  deriving (Generic)
