indexing
	description: "The rendering engine that keeps track of all animations."

class
	ANIMATION_ENGINE

feature -- Queries

	-- What is your welcome animation?
	welcome_animation: WELCOME_ANIMATION

	-- What is your star animation?
	star_animation: STAR_ANIMATION

	-- What is your explosion animation?
	explosion_animation: EXPLOSION_ANIMATION

	-- What is your barrier animation?
	barrier_animation: BARRIER_ANIMATION

	-- What is your factory animation?
	factory_animation: FACTORY_ANIMATION

	-- What is your escape animation?
	escape_animation: ESCAPE_ANIMATION

feature -- Commands

invariant -- Constraints

end
