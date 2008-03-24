#ifdef __TEST__

	void Frame::RunTest(void)
	{

		Frame * frameA = new Frame(0, 0, 0, 0);
		Frame * frameB = new Frame(7, 7, 7, 7);
		Frame * frameC;
		Frame * frameD;
		Frame * frame;

		std::cout << "Two new frames" << std::endl;
		std::cout << frameA << std::endl;
		std::cout << frameB << std::endl;

		std::cout << "Append frameA to frameB" << std::endl;
		(*frameA) += frameB;

		std::cout << "Updated frames" << std::endl;
		std::cout << frameA << std::endl;
		std::cout << frameB << std::endl;

		std::cout << "Store frameA in frameC" << std::endl;
		frameC = frameA;
		std::cout << "Erase one frame from C and store new C" << std::endl;
		frameC = frameC->erase(0);
		std::cout << "Output A and C" << std::endl;
		std::cout << (void*)frameA << std::endl;
		std::cout << (void*)frameC << std::endl;
		std::cout << "Erase another frame from C and store in C" << std::endl;
		frameC = frameC->erase(0);
		std::cout << "Output C" << std::endl;
		std::cout << frameC << std::endl;
		std::cout << "Erase another frame from C and store in C" << std::endl;
		frameC = frameC->erase(0);

		frameA = new Frame(1, 1, 1, 0);
		frameB = new Frame(2, 2, 2, 0);
		frameC = new Frame(3, 3, 3, 0);
		frameD = new Frame(4, 4, 4, 0);

		(*frameA) += frameB;
		(*frameC) += frameD;

		std::cout << "Attach frame groups A(1)->B(2) and C(3)->D(4) on A, so it's A->C->D->B" << std::endl;
		(*frameA) += frameC;
		std::cout << "Iterate frames" << std::endl;
		for(frame = frameA; frame != 0; frame = frame->next())
			std::cout << frame << std::endl;

		std::cout << "Get the total number of frames from the POV of A, B, and C" << std::endl;
		std::cout << frameA->length() << ", " << frameB->length() << ", " << frameC->length() << std::endl;

		std::cout << "What is the last frame from POV of A, B, and C" << std::endl;
		std::cout << frameA->last() << std::endl << frameB->last() << std::endl << frameC->last() << std::endl;

		std::cout << "Get frame A to erase 2 frames and update so frame A points to the start of the new list" << std::endl;
		// erase(1) - 1 means frame index, so erases frames 0 and 1
		frameA = frameA->erase(1);
		for(frame = frameA; frame != 0; frame = frame->next())
			std::cout << frame << std::endl;

		std::cout << "Erase all frames" << std::endl;
		frameA = frameA->erase();
		for(frame = frameA; frame != 0; frame = frame->next())
			std::cout << frame << std::endl;

	// Don't know how to run this test in linux as I only know how VC automatically modifies deleted memory
#	ifdef WIN32

		std::cout << "Create 3 frames joined together" << std::endl;
		frameA = new Frame(1, 1, 1, 0);
		frameB = new Frame(2, 2, 2, 0);
		frameC = new Frame(3, 3, 3, 0);
		(*((*frameA) += frameB)) += frameC;

		std::cout << "Is memory allocated for all" << std::endl;
		std::cout << (frameA->_time == 0) << ", " << (frameB->_time == 0) << ", " << (frameC->_time == 0) << std::endl;

		std::cout << "Delete the first one" << std::endl;
		delete frameA;

		std::cout << "Is memory allocated for all" << std::endl;
		std::cout << (frameA->_time == 0) << ", " << (frameB->_time == 0) << ", " << (frameC->_time == 0) << std::endl;

#	endif

	}

#endif
