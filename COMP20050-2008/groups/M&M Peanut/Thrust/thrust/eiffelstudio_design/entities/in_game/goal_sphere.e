indexing
	description: "The goal sphere that the spaceship needs to town to escape."

class
	GOAL_SPHERE

inherit
	NEUTRAL_ENTITY
	DYNAMIC_ENTITY
	TOW

feature -- Queries

feature -- Commands

invariant -- Constraints
	-- The fuel pod is destroyed by a bullet.
	-- If the fuel pod is destroyed, the spaceship is destroyed.
	-- The goal sphere is destroyed by the factory's chimney, but not its sphere.
	-- The goal sphere is not affected by the gun turrent.
	-- The goal sphere is not affected by the fuel pod.
	-- The goal sphere is not affected by space.
	-- The goal sphere is not affected by stars.
	-- The goal sphere is destroyed by the terrain.
	-- When rendered on the terrain, the goal sphere sits on a pedestal.
	-- When being towed, the goal sphere is rendered as a sphere.
	-- The shape of the goal sphere is always a circle.
	-- The color of the goal sphere is always green.

end
