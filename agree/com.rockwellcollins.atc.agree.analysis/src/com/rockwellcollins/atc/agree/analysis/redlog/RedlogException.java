package com.rockwellcollins.atc.agree.analysis.redlog;

public class RedlogException extends RuntimeException {
	private static final long serialVersionUID = 1L;

	public RedlogException(String message) {
		super(message);
	}
	
	public RedlogException(String message, Throwable t) {
		super(message, t);
	}

}
