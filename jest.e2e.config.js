module.exports = {
  testEnvironment: 'node',
  testMatch: ['**/tests/e2e/**/*.test.js'],
  setupFilesAfterEnv: ['<rootDir>/tests/setup/e2e-setup.js'],
  testTimeout: 30000,
  verbose: true,
  collectCoverageFrom: [
    'scripts/**/*.js',
    '!scripts/test*.js',
    '!**/node_modules/**'
  ],
  coverageDirectory: 'coverage/e2e',
  coverageReporters: ['text', 'lcov', 'html']
};
