indexing
	description: "The highest scores ever recorded in the game."

class
	HIGH_SCORES

inherit
	STORABLE

feature -- Queries
	-- What are the current high scores?

feature -- Commands
	-- Insert the score and player '(s,p)' in the high score list.

invariant -- Constraints
	-- High scores are always arranged from highest to lowest score.
	-- There are eight recorded high scores.
	-- The initial high scores are pre-determined.

end
