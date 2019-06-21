import logging
logging.basicConfig()
logger = logging.getLogger('Crash-free-fix ')
logger.setLevel(logging.DEBUG)
logger.debug('This message should go to the log file')
logger.info('So should this')
logger.warning('And this, too')
