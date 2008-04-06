indexing
	description: "A chimney of a factory."

class
	FACTORY_CHIMNEY

inherit
	NEUTRAL_ENTITY
	STATIC_ENTITY
	ANIMATABLE

feature -- Queries
	-- Are you smoking?

feature -- Commands

invariant -- Constraints
	-- The goal sphere is destroyed by a factory's chimney.
	-- The spaceship is destroyed by a factory's chimney.

end
