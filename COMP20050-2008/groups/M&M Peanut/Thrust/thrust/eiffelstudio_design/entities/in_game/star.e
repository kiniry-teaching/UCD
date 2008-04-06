indexing
	description: "A blinking star in space."

class
	STAR

inherit
	NEUTRAL_ENTITY
	STATIC_ENTITY
	ANIMATABLE

feature -- Queries

feature -- Commands

invariant -- Constraints
	-- A star interacts with no other entities.
	-- Each star blinks irregularly via a blinking star animation.
	-- A star's shape is always a small square.

end
