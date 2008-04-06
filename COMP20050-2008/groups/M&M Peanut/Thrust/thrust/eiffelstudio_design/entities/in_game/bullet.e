indexing
	description: "A bullet shot from the spaceship or a gun turrent."

class
	BULLET

inherit
	ENEMY_ENTITY
	DYNAMIC_ENTITY

feature -- Queries

feature -- Commands

invariant -- Constraints
	-- Bullets are destroyed on contact with a barrier, a factory, a fuel pod, the goal sphere,
	--   a gun turrent, the spaceship, or the terrain.
	-- Bullets have a mass of 1 kg.

end
