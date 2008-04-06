indexing
	description: "Processes and delegates each keyboard input received."

class
	INPUT_HANDLER

feature -- Access

	keyboard_inputs: LIST[KEYBOARD_INPUT]

feature -- Queries

feature -- Commands

invariant -- Constraints
	-- One can only start the game while the high score list is being shown.
	-- Asking for the high score list only works during the game demo.
	-- Player input only works while the game is being played.

end
